%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:01 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 250 expanded)
%              Number of leaves         :   46 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :  195 ( 587 expanded)
%              Number of equality atoms :   36 ( 110 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_140,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_74,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_133,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_147,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_133])).

tff(c_36,plain,(
    ! [A_25] :
      ( k9_relat_1(A_25,k1_relat_1(A_25)) = k2_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_819,plain,(
    ! [A_182,B_183,C_184] :
      ( r2_hidden(k4_tarski('#skF_2'(A_182,B_183,C_184),A_182),C_184)
      | ~ r2_hidden(A_182,k9_relat_1(C_184,B_183))
      | ~ v1_relat_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_864,plain,(
    ! [C_185,A_186,B_187] :
      ( ~ v1_xboole_0(C_185)
      | ~ r2_hidden(A_186,k9_relat_1(C_185,B_187))
      | ~ v1_relat_1(C_185) ) ),
    inference(resolution,[status(thm)],[c_819,c_2])).

tff(c_888,plain,(
    ! [C_188,B_189] :
      ( ~ v1_xboole_0(C_188)
      | ~ v1_relat_1(C_188)
      | v1_xboole_0(k9_relat_1(C_188,B_189)) ) ),
    inference(resolution,[status(thm)],[c_4,c_864])).

tff(c_892,plain,(
    ! [A_190] :
      ( ~ v1_xboole_0(A_190)
      | ~ v1_relat_1(A_190)
      | v1_xboole_0(k2_relat_1(A_190))
      | ~ v1_relat_1(A_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_888])).

tff(c_221,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_235,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_221])).

tff(c_72,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_86,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_237,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_86])).

tff(c_901,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_892,c_237])).

tff(c_908,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_901])).

tff(c_1493,plain,(
    ! [A_264,B_265,C_266,D_267] :
      ( r2_hidden('#skF_4'(A_264,B_265,C_266,D_267),C_266)
      | ~ r2_hidden(A_264,D_267)
      | ~ m1_subset_1(D_267,k1_zfmisc_1(k2_zfmisc_1(B_265,C_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1509,plain,(
    ! [A_268] :
      ( r2_hidden('#skF_4'(A_268,'#skF_6','#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_268,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_74,c_1493])).

tff(c_1517,plain,(
    ! [A_268] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_268,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1509,c_2])).

tff(c_1518,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1517])).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_179,plain,(
    ! [B_77,A_78] :
      ( v5_relat_1(B_77,A_78)
      | ~ r1_tarski(k2_relat_1(B_77),A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_184,plain,(
    ! [B_77] :
      ( v5_relat_1(B_77,k2_relat_1(B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_12,c_179])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_312,plain,(
    ! [C_103,A_104,B_105] :
      ( v5_relat_1(C_103,A_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(B_105))
      | ~ v5_relat_1(B_105,A_104)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_376,plain,(
    ! [A_112,A_113,B_114] :
      ( v5_relat_1(A_112,A_113)
      | ~ v5_relat_1(B_114,A_113)
      | ~ v1_relat_1(B_114)
      | ~ r1_tarski(A_112,B_114) ) ),
    inference(resolution,[status(thm)],[c_18,c_312])).

tff(c_385,plain,(
    ! [A_115,B_116] :
      ( v5_relat_1(A_115,k2_relat_1(B_116))
      | ~ r1_tarski(A_115,B_116)
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_184,c_376])).

tff(c_238,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_72])).

tff(c_325,plain,(
    ! [C_106,A_107,B_108] :
      ( r2_hidden(C_106,A_107)
      | ~ r2_hidden(C_106,k2_relat_1(B_108))
      | ~ v5_relat_1(B_108,A_107)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_327,plain,(
    ! [A_107] :
      ( r2_hidden('#skF_5',A_107)
      | ~ v5_relat_1('#skF_8',A_107)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_238,c_325])).

tff(c_333,plain,(
    ! [A_107] :
      ( r2_hidden('#skF_5',A_107)
      | ~ v5_relat_1('#skF_8',A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_327])).

tff(c_403,plain,(
    ! [B_116] :
      ( r2_hidden('#skF_5',k2_relat_1(B_116))
      | ~ r1_tarski('#skF_8',B_116)
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_385,c_333])).

tff(c_76,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_202,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_216,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_202])).

tff(c_1943,plain,(
    ! [B_322,A_323,C_324] :
      ( k1_xboole_0 = B_322
      | k1_relset_1(A_323,B_322,C_324) = A_323
      | ~ v1_funct_2(C_324,A_323,B_322)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_323,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1958,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_1943])).

tff(c_1964,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_216,c_1958])).

tff(c_1965,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1964])).

tff(c_1992,plain,
    ( k9_relat_1('#skF_8','#skF_6') = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1965,c_36])).

tff(c_2011,plain,(
    k9_relat_1('#skF_8','#skF_6') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1992])).

tff(c_557,plain,(
    ! [A_140,B_141,C_142] :
      ( r2_hidden('#skF_2'(A_140,B_141,C_142),B_141)
      | ~ r2_hidden(A_140,k9_relat_1(C_142,B_141))
      | ~ v1_relat_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_568,plain,(
    ! [A_140,B_141,C_142] :
      ( m1_subset_1('#skF_2'(A_140,B_141,C_142),B_141)
      | ~ r2_hidden(A_140,k9_relat_1(C_142,B_141))
      | ~ v1_relat_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_557,c_14])).

tff(c_2089,plain,(
    ! [A_140] :
      ( m1_subset_1('#skF_2'(A_140,'#skF_6','#skF_8'),'#skF_6')
      | ~ r2_hidden(A_140,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2011,c_568])).

tff(c_2220,plain,(
    ! [A_335] :
      ( m1_subset_1('#skF_2'(A_335,'#skF_6','#skF_8'),'#skF_6')
      | ~ r2_hidden(A_335,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2089])).

tff(c_2248,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_8'),'#skF_6')
    | ~ r1_tarski('#skF_8','#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_403,c_2220])).

tff(c_2266,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_12,c_2248])).

tff(c_70,plain,(
    ! [E_52] :
      ( k1_funct_1('#skF_8',E_52) != '#skF_5'
      | ~ m1_subset_1(E_52,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2274,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_5','#skF_6','#skF_8')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_2266,c_70])).

tff(c_78,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_42,plain,(
    ! [C_32,A_30,B_31] :
      ( k1_funct_1(C_32,A_30) = B_31
      | ~ r2_hidden(k4_tarski(A_30,B_31),C_32)
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3024,plain,(
    ! [C_417,A_418,B_419] :
      ( k1_funct_1(C_417,'#skF_2'(A_418,B_419,C_417)) = A_418
      | ~ v1_funct_1(C_417)
      | ~ r2_hidden(A_418,k9_relat_1(C_417,B_419))
      | ~ v1_relat_1(C_417) ) ),
    inference(resolution,[status(thm)],[c_819,c_42])).

tff(c_3029,plain,(
    ! [A_418] :
      ( k1_funct_1('#skF_8','#skF_2'(A_418,'#skF_6','#skF_8')) = A_418
      | ~ v1_funct_1('#skF_8')
      | ~ r2_hidden(A_418,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2011,c_3024])).

tff(c_3059,plain,(
    ! [A_420] :
      ( k1_funct_1('#skF_8','#skF_2'(A_420,'#skF_6','#skF_8')) = A_420
      | ~ r2_hidden(A_420,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_78,c_3029])).

tff(c_3091,plain,
    ( k1_funct_1('#skF_8','#skF_2'('#skF_5','#skF_6','#skF_8')) = '#skF_5'
    | ~ r1_tarski('#skF_8','#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_403,c_3059])).

tff(c_3111,plain,(
    k1_funct_1('#skF_8','#skF_2'('#skF_5','#skF_6','#skF_8')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_12,c_3091])).

tff(c_3113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2274,c_3111])).

tff(c_3114,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1964])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3129,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3114,c_6])).

tff(c_3131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1518,c_3129])).

tff(c_3135,plain,(
    ! [A_422] : ~ r2_hidden(A_422,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1517])).

tff(c_3155,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_3135])).

tff(c_3167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_908,c_3155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:06:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/1.95  
% 5.18/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/1.95  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 5.18/1.95  
% 5.18/1.95  %Foreground sorts:
% 5.18/1.95  
% 5.18/1.95  
% 5.18/1.95  %Background operators:
% 5.18/1.95  
% 5.18/1.95  
% 5.18/1.95  %Foreground operators:
% 5.18/1.95  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.18/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.18/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.18/1.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.18/1.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.18/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.18/1.95  tff('#skF_7', type, '#skF_7': $i).
% 5.18/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.18/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.18/1.95  tff('#skF_5', type, '#skF_5': $i).
% 5.18/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.18/1.95  tff('#skF_6', type, '#skF_6': $i).
% 5.18/1.95  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.18/1.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.18/1.95  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.18/1.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.18/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.18/1.95  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.18/1.95  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.18/1.95  tff('#skF_8', type, '#skF_8': $i).
% 5.18/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.18/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.18/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/1.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.18/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.18/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.18/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.18/1.95  
% 5.18/1.97  tff(f_156, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 5.18/1.97  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.18/1.97  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.18/1.97  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.18/1.97  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 5.18/1.97  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.18/1.97  tff(f_122, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 5.18/1.97  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.18/1.97  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.18/1.97  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.18/1.97  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_relat_1)).
% 5.18/1.97  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 5.18/1.97  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.18/1.97  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.18/1.97  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.18/1.97  tff(f_97, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 5.18/1.97  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.18/1.97  tff(c_74, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.18/1.97  tff(c_133, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.18/1.97  tff(c_147, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_133])).
% 5.18/1.97  tff(c_36, plain, (![A_25]: (k9_relat_1(A_25, k1_relat_1(A_25))=k2_relat_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.18/1.97  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.18/1.97  tff(c_819, plain, (![A_182, B_183, C_184]: (r2_hidden(k4_tarski('#skF_2'(A_182, B_183, C_184), A_182), C_184) | ~r2_hidden(A_182, k9_relat_1(C_184, B_183)) | ~v1_relat_1(C_184))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.18/1.97  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.18/1.97  tff(c_864, plain, (![C_185, A_186, B_187]: (~v1_xboole_0(C_185) | ~r2_hidden(A_186, k9_relat_1(C_185, B_187)) | ~v1_relat_1(C_185))), inference(resolution, [status(thm)], [c_819, c_2])).
% 5.18/1.97  tff(c_888, plain, (![C_188, B_189]: (~v1_xboole_0(C_188) | ~v1_relat_1(C_188) | v1_xboole_0(k9_relat_1(C_188, B_189)))), inference(resolution, [status(thm)], [c_4, c_864])).
% 5.18/1.97  tff(c_892, plain, (![A_190]: (~v1_xboole_0(A_190) | ~v1_relat_1(A_190) | v1_xboole_0(k2_relat_1(A_190)) | ~v1_relat_1(A_190))), inference(superposition, [status(thm), theory('equality')], [c_36, c_888])).
% 5.18/1.97  tff(c_221, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.18/1.97  tff(c_235, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_221])).
% 5.18/1.97  tff(c_72, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.18/1.97  tff(c_86, plain, (~v1_xboole_0(k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_72, c_2])).
% 5.18/1.97  tff(c_237, plain, (~v1_xboole_0(k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_86])).
% 5.18/1.97  tff(c_901, plain, (~v1_xboole_0('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_892, c_237])).
% 5.18/1.97  tff(c_908, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_901])).
% 5.18/1.97  tff(c_1493, plain, (![A_264, B_265, C_266, D_267]: (r2_hidden('#skF_4'(A_264, B_265, C_266, D_267), C_266) | ~r2_hidden(A_264, D_267) | ~m1_subset_1(D_267, k1_zfmisc_1(k2_zfmisc_1(B_265, C_266))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.18/1.97  tff(c_1509, plain, (![A_268]: (r2_hidden('#skF_4'(A_268, '#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_268, '#skF_8'))), inference(resolution, [status(thm)], [c_74, c_1493])).
% 5.18/1.97  tff(c_1517, plain, (![A_268]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_268, '#skF_8'))), inference(resolution, [status(thm)], [c_1509, c_2])).
% 5.18/1.97  tff(c_1518, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1517])).
% 5.18/1.97  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.18/1.97  tff(c_179, plain, (![B_77, A_78]: (v5_relat_1(B_77, A_78) | ~r1_tarski(k2_relat_1(B_77), A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.18/1.97  tff(c_184, plain, (![B_77]: (v5_relat_1(B_77, k2_relat_1(B_77)) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_12, c_179])).
% 5.18/1.97  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.18/1.97  tff(c_312, plain, (![C_103, A_104, B_105]: (v5_relat_1(C_103, A_104) | ~m1_subset_1(C_103, k1_zfmisc_1(B_105)) | ~v5_relat_1(B_105, A_104) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.18/1.97  tff(c_376, plain, (![A_112, A_113, B_114]: (v5_relat_1(A_112, A_113) | ~v5_relat_1(B_114, A_113) | ~v1_relat_1(B_114) | ~r1_tarski(A_112, B_114))), inference(resolution, [status(thm)], [c_18, c_312])).
% 5.18/1.97  tff(c_385, plain, (![A_115, B_116]: (v5_relat_1(A_115, k2_relat_1(B_116)) | ~r1_tarski(A_115, B_116) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_184, c_376])).
% 5.18/1.97  tff(c_238, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_72])).
% 5.18/1.97  tff(c_325, plain, (![C_106, A_107, B_108]: (r2_hidden(C_106, A_107) | ~r2_hidden(C_106, k2_relat_1(B_108)) | ~v5_relat_1(B_108, A_107) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.18/1.97  tff(c_327, plain, (![A_107]: (r2_hidden('#skF_5', A_107) | ~v5_relat_1('#skF_8', A_107) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_238, c_325])).
% 5.18/1.97  tff(c_333, plain, (![A_107]: (r2_hidden('#skF_5', A_107) | ~v5_relat_1('#skF_8', A_107))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_327])).
% 5.18/1.97  tff(c_403, plain, (![B_116]: (r2_hidden('#skF_5', k2_relat_1(B_116)) | ~r1_tarski('#skF_8', B_116) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_385, c_333])).
% 5.18/1.97  tff(c_76, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.18/1.97  tff(c_202, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.18/1.97  tff(c_216, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_202])).
% 5.18/1.97  tff(c_1943, plain, (![B_322, A_323, C_324]: (k1_xboole_0=B_322 | k1_relset_1(A_323, B_322, C_324)=A_323 | ~v1_funct_2(C_324, A_323, B_322) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_323, B_322))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.18/1.97  tff(c_1958, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_1943])).
% 5.18/1.97  tff(c_1964, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_216, c_1958])).
% 5.18/1.97  tff(c_1965, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_1964])).
% 5.18/1.97  tff(c_1992, plain, (k9_relat_1('#skF_8', '#skF_6')=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1965, c_36])).
% 5.18/1.97  tff(c_2011, plain, (k9_relat_1('#skF_8', '#skF_6')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_1992])).
% 5.18/1.97  tff(c_557, plain, (![A_140, B_141, C_142]: (r2_hidden('#skF_2'(A_140, B_141, C_142), B_141) | ~r2_hidden(A_140, k9_relat_1(C_142, B_141)) | ~v1_relat_1(C_142))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.18/1.97  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.18/1.97  tff(c_568, plain, (![A_140, B_141, C_142]: (m1_subset_1('#skF_2'(A_140, B_141, C_142), B_141) | ~r2_hidden(A_140, k9_relat_1(C_142, B_141)) | ~v1_relat_1(C_142))), inference(resolution, [status(thm)], [c_557, c_14])).
% 5.18/1.97  tff(c_2089, plain, (![A_140]: (m1_subset_1('#skF_2'(A_140, '#skF_6', '#skF_8'), '#skF_6') | ~r2_hidden(A_140, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2011, c_568])).
% 5.18/1.97  tff(c_2220, plain, (![A_335]: (m1_subset_1('#skF_2'(A_335, '#skF_6', '#skF_8'), '#skF_6') | ~r2_hidden(A_335, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2089])).
% 5.18/1.97  tff(c_2248, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_6', '#skF_8'), '#skF_6') | ~r1_tarski('#skF_8', '#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_403, c_2220])).
% 5.18/1.97  tff(c_2266, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_6', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_12, c_2248])).
% 5.18/1.97  tff(c_70, plain, (![E_52]: (k1_funct_1('#skF_8', E_52)!='#skF_5' | ~m1_subset_1(E_52, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.18/1.97  tff(c_2274, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_5', '#skF_6', '#skF_8'))!='#skF_5'), inference(resolution, [status(thm)], [c_2266, c_70])).
% 5.18/1.97  tff(c_78, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.18/1.97  tff(c_42, plain, (![C_32, A_30, B_31]: (k1_funct_1(C_32, A_30)=B_31 | ~r2_hidden(k4_tarski(A_30, B_31), C_32) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.18/1.97  tff(c_3024, plain, (![C_417, A_418, B_419]: (k1_funct_1(C_417, '#skF_2'(A_418, B_419, C_417))=A_418 | ~v1_funct_1(C_417) | ~r2_hidden(A_418, k9_relat_1(C_417, B_419)) | ~v1_relat_1(C_417))), inference(resolution, [status(thm)], [c_819, c_42])).
% 5.18/1.97  tff(c_3029, plain, (![A_418]: (k1_funct_1('#skF_8', '#skF_2'(A_418, '#skF_6', '#skF_8'))=A_418 | ~v1_funct_1('#skF_8') | ~r2_hidden(A_418, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2011, c_3024])).
% 5.18/1.97  tff(c_3059, plain, (![A_420]: (k1_funct_1('#skF_8', '#skF_2'(A_420, '#skF_6', '#skF_8'))=A_420 | ~r2_hidden(A_420, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_78, c_3029])).
% 5.18/1.97  tff(c_3091, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_5', '#skF_6', '#skF_8'))='#skF_5' | ~r1_tarski('#skF_8', '#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_403, c_3059])).
% 5.18/1.97  tff(c_3111, plain, (k1_funct_1('#skF_8', '#skF_2'('#skF_5', '#skF_6', '#skF_8'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_12, c_3091])).
% 5.18/1.97  tff(c_3113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2274, c_3111])).
% 5.18/1.97  tff(c_3114, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1964])).
% 5.18/1.97  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.18/1.97  tff(c_3129, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3114, c_6])).
% 5.18/1.97  tff(c_3131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1518, c_3129])).
% 5.18/1.97  tff(c_3135, plain, (![A_422]: (~r2_hidden(A_422, '#skF_8'))), inference(splitRight, [status(thm)], [c_1517])).
% 5.18/1.97  tff(c_3155, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_3135])).
% 5.18/1.97  tff(c_3167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_908, c_3155])).
% 5.18/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/1.97  
% 5.18/1.97  Inference rules
% 5.18/1.97  ----------------------
% 5.18/1.97  #Ref     : 0
% 5.18/1.97  #Sup     : 638
% 5.18/1.97  #Fact    : 0
% 5.18/1.97  #Define  : 0
% 5.18/1.97  #Split   : 11
% 5.18/1.97  #Chain   : 0
% 5.18/1.97  #Close   : 0
% 5.18/1.97  
% 5.18/1.97  Ordering : KBO
% 5.18/1.97  
% 5.18/1.97  Simplification rules
% 5.18/1.97  ----------------------
% 5.18/1.97  #Subsume      : 135
% 5.18/1.97  #Demod        : 211
% 5.18/1.97  #Tautology    : 45
% 5.18/1.97  #SimpNegUnit  : 26
% 5.18/1.97  #BackRed      : 19
% 5.18/1.97  
% 5.18/1.97  #Partial instantiations: 0
% 5.18/1.97  #Strategies tried      : 1
% 5.18/1.97  
% 5.18/1.97  Timing (in seconds)
% 5.18/1.97  ----------------------
% 5.18/1.97  Preprocessing        : 0.35
% 5.18/1.97  Parsing              : 0.19
% 5.18/1.97  CNF conversion       : 0.02
% 5.18/1.97  Main loop            : 0.85
% 5.18/1.97  Inferencing          : 0.29
% 5.18/1.97  Reduction            : 0.24
% 5.18/1.97  Demodulation         : 0.16
% 5.18/1.97  BG Simplification    : 0.04
% 5.18/1.97  Subsumption          : 0.21
% 5.18/1.97  Abstraction          : 0.04
% 5.18/1.97  MUC search           : 0.00
% 5.18/1.97  Cooper               : 0.00
% 5.18/1.98  Total                : 1.25
% 5.18/1.98  Index Insertion      : 0.00
% 5.18/1.98  Index Deletion       : 0.00
% 5.18/1.98  Index Matching       : 0.00
% 5.18/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
