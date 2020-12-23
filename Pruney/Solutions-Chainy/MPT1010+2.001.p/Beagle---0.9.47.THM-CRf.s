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
% DateTime   : Thu Dec  3 10:15:05 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 122 expanded)
%              Number of leaves         :   48 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  124 ( 218 expanded)
%              Number of equality atoms :   43 (  81 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_11 > #skF_1 > #skF_8 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_5 > #skF_6 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_173,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_144,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_162,axiom,(
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

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_123,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_106,plain,(
    k1_funct_1('#skF_12','#skF_11') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_110,plain,(
    m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_9',k1_tarski('#skF_10')))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_506,plain,(
    ! [C_159,B_160,A_161] :
      ( v5_relat_1(C_159,B_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_526,plain,(
    v5_relat_1('#skF_12',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_110,c_506])).

tff(c_108,plain,(
    r2_hidden('#skF_11','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_376,plain,(
    ! [C_130,A_131,B_132] :
      ( v1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_384,plain,(
    v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_110,c_376])).

tff(c_114,plain,(
    v1_funct_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_112,plain,(
    v1_funct_2('#skF_12','#skF_9',k1_tarski('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_908,plain,(
    ! [A_209,B_210,C_211] :
      ( k1_relset_1(A_209,B_210,C_211) = k1_relat_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_938,plain,(
    k1_relset_1('#skF_9',k1_tarski('#skF_10'),'#skF_12') = k1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_110,c_908])).

tff(c_1849,plain,(
    ! [B_280,A_281,C_282] :
      ( k1_xboole_0 = B_280
      | k1_relset_1(A_281,B_280,C_282) = A_281
      | ~ v1_funct_2(C_282,A_281,B_280)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_281,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1868,plain,
    ( k1_tarski('#skF_10') = k1_xboole_0
    | k1_relset_1('#skF_9',k1_tarski('#skF_10'),'#skF_12') = '#skF_9'
    | ~ v1_funct_2('#skF_12','#skF_9',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_110,c_1849])).

tff(c_1881,plain,
    ( k1_tarski('#skF_10') = k1_xboole_0
    | k1_relat_1('#skF_12') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_938,c_1868])).

tff(c_1893,plain,(
    k1_relat_1('#skF_12') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1881])).

tff(c_72,plain,(
    ! [C_38,B_37,A_36] :
      ( m1_subset_1(k1_funct_1(C_38,B_37),A_36)
      | ~ r2_hidden(B_37,k1_relat_1(C_38))
      | ~ v1_funct_1(C_38)
      | ~ v5_relat_1(C_38,A_36)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1897,plain,(
    ! [B_37,A_36] :
      ( m1_subset_1(k1_funct_1('#skF_12',B_37),A_36)
      | ~ r2_hidden(B_37,'#skF_9')
      | ~ v1_funct_1('#skF_12')
      | ~ v5_relat_1('#skF_12',A_36)
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1893,c_72])).

tff(c_2016,plain,(
    ! [B_289,A_290] :
      ( m1_subset_1(k1_funct_1('#skF_12',B_289),A_290)
      | ~ r2_hidden(B_289,'#skF_9')
      | ~ v5_relat_1('#skF_12',A_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_114,c_1897])).

tff(c_34,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_245,plain,(
    ! [A_107,B_108] : k1_enumset1(A_107,A_107,B_108) = k2_tarski(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_157,plain,(
    ! [E_74,A_75,C_76] : r2_hidden(E_74,k1_enumset1(A_75,E_74,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [A_75,E_74,C_76] : ~ v1_xboole_0(k1_enumset1(A_75,E_74,C_76)) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_268,plain,(
    ! [A_107,B_108] : ~ v1_xboole_0(k2_tarski(A_107,B_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_161])).

tff(c_62,plain,(
    ! [A_29,B_30] :
      ( r2_hidden(A_29,B_30)
      | v1_xboole_0(B_30)
      | ~ m1_subset_1(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_647,plain,(
    ! [E_182,C_183,B_184,A_185] :
      ( E_182 = C_183
      | E_182 = B_184
      | E_182 = A_185
      | ~ r2_hidden(E_182,k1_enumset1(A_185,B_184,C_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1353,plain,(
    ! [E_248,B_249,A_250] :
      ( E_248 = B_249
      | E_248 = A_250
      | E_248 = A_250
      | ~ r2_hidden(E_248,k2_tarski(A_250,B_249)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_647])).

tff(c_1373,plain,(
    ! [B_249,A_29,A_250] :
      ( B_249 = A_29
      | A_29 = A_250
      | v1_xboole_0(k2_tarski(A_250,B_249))
      | ~ m1_subset_1(A_29,k2_tarski(A_250,B_249)) ) ),
    inference(resolution,[status(thm)],[c_62,c_1353])).

tff(c_1401,plain,(
    ! [B_251,A_252,A_253] :
      ( B_251 = A_252
      | A_253 = A_252
      | ~ m1_subset_1(A_252,k2_tarski(A_253,B_251)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_1373])).

tff(c_1422,plain,(
    ! [A_252,A_13] :
      ( A_252 = A_13
      | A_252 = A_13
      | ~ m1_subset_1(A_252,k1_tarski(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1401])).

tff(c_2351,plain,(
    ! [B_311,A_312] :
      ( k1_funct_1('#skF_12',B_311) = A_312
      | ~ r2_hidden(B_311,'#skF_9')
      | ~ v5_relat_1('#skF_12',k1_tarski(A_312)) ) ),
    inference(resolution,[status(thm)],[c_2016,c_1422])).

tff(c_2390,plain,(
    ! [A_313] :
      ( k1_funct_1('#skF_12','#skF_11') = A_313
      | ~ v5_relat_1('#skF_12',k1_tarski(A_313)) ) ),
    inference(resolution,[status(thm)],[c_108,c_2351])).

tff(c_2396,plain,(
    k1_funct_1('#skF_12','#skF_11') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_526,c_2390])).

tff(c_2401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_2396])).

tff(c_2402,plain,(
    k1_tarski('#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1881])).

tff(c_12,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_280,plain,(
    ! [B_111,A_112] : r2_hidden(B_111,k2_tarski(A_112,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_12])).

tff(c_296,plain,(
    ! [A_113] : r2_hidden(A_113,k1_tarski(A_113)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_280])).

tff(c_82,plain,(
    ! [B_50,A_49] :
      ( ~ r1_tarski(B_50,A_49)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_307,plain,(
    ! [A_113] : ~ r1_tarski(k1_tarski(A_113),A_113) ),
    inference(resolution,[status(thm)],[c_296,c_82])).

tff(c_2427,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2402,c_307])).

tff(c_2440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2427])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:27:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.64/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.85  
% 4.64/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.86  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_11 > #skF_1 > #skF_8 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_5 > #skF_6 > #skF_12 > #skF_4
% 4.64/1.86  
% 4.64/1.86  %Foreground sorts:
% 4.64/1.86  
% 4.64/1.86  
% 4.64/1.86  %Background operators:
% 4.64/1.86  
% 4.64/1.86  
% 4.64/1.86  %Foreground operators:
% 4.64/1.86  tff('#skF_7', type, '#skF_7': $i > $i).
% 4.64/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.64/1.86  tff('#skF_11', type, '#skF_11': $i).
% 4.64/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.64/1.86  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.64/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.64/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.64/1.86  tff('#skF_8', type, '#skF_8': $i > $i).
% 4.64/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.64/1.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.64/1.86  tff('#skF_10', type, '#skF_10': $i).
% 4.64/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.64/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.64/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.64/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.64/1.86  tff('#skF_9', type, '#skF_9': $i).
% 4.64/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.64/1.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.64/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.64/1.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.64/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.64/1.86  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.64/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.64/1.86  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.64/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.64/1.86  tff('#skF_6', type, '#skF_6': $i > $i).
% 4.64/1.86  tff('#skF_12', type, '#skF_12': $i).
% 4.64/1.86  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.64/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.64/1.86  
% 4.64/1.87  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.64/1.87  tff(f_173, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 4.64/1.87  tff(f_133, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.64/1.87  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.64/1.87  tff(f_144, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.64/1.87  tff(f_162, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.64/1.87  tff(f_109, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 4.64/1.87  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.64/1.87  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.64/1.87  tff(f_49, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.64/1.87  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.64/1.87  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.64/1.87  tff(f_123, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.64/1.87  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.64/1.87  tff(c_106, plain, (k1_funct_1('#skF_12', '#skF_11')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.64/1.87  tff(c_110, plain, (m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_9', k1_tarski('#skF_10'))))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.64/1.87  tff(c_506, plain, (![C_159, B_160, A_161]: (v5_relat_1(C_159, B_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.64/1.87  tff(c_526, plain, (v5_relat_1('#skF_12', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_110, c_506])).
% 4.64/1.87  tff(c_108, plain, (r2_hidden('#skF_11', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.64/1.87  tff(c_376, plain, (![C_130, A_131, B_132]: (v1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.64/1.87  tff(c_384, plain, (v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_110, c_376])).
% 4.64/1.87  tff(c_114, plain, (v1_funct_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.64/1.87  tff(c_112, plain, (v1_funct_2('#skF_12', '#skF_9', k1_tarski('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.64/1.87  tff(c_908, plain, (![A_209, B_210, C_211]: (k1_relset_1(A_209, B_210, C_211)=k1_relat_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.87  tff(c_938, plain, (k1_relset_1('#skF_9', k1_tarski('#skF_10'), '#skF_12')=k1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_110, c_908])).
% 4.64/1.87  tff(c_1849, plain, (![B_280, A_281, C_282]: (k1_xboole_0=B_280 | k1_relset_1(A_281, B_280, C_282)=A_281 | ~v1_funct_2(C_282, A_281, B_280) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_281, B_280))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.64/1.87  tff(c_1868, plain, (k1_tarski('#skF_10')=k1_xboole_0 | k1_relset_1('#skF_9', k1_tarski('#skF_10'), '#skF_12')='#skF_9' | ~v1_funct_2('#skF_12', '#skF_9', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_110, c_1849])).
% 4.64/1.87  tff(c_1881, plain, (k1_tarski('#skF_10')=k1_xboole_0 | k1_relat_1('#skF_12')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_938, c_1868])).
% 4.64/1.87  tff(c_1893, plain, (k1_relat_1('#skF_12')='#skF_9'), inference(splitLeft, [status(thm)], [c_1881])).
% 4.64/1.87  tff(c_72, plain, (![C_38, B_37, A_36]: (m1_subset_1(k1_funct_1(C_38, B_37), A_36) | ~r2_hidden(B_37, k1_relat_1(C_38)) | ~v1_funct_1(C_38) | ~v5_relat_1(C_38, A_36) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.64/1.87  tff(c_1897, plain, (![B_37, A_36]: (m1_subset_1(k1_funct_1('#skF_12', B_37), A_36) | ~r2_hidden(B_37, '#skF_9') | ~v1_funct_1('#skF_12') | ~v5_relat_1('#skF_12', A_36) | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1893, c_72])).
% 4.64/1.87  tff(c_2016, plain, (![B_289, A_290]: (m1_subset_1(k1_funct_1('#skF_12', B_289), A_290) | ~r2_hidden(B_289, '#skF_9') | ~v5_relat_1('#skF_12', A_290))), inference(demodulation, [status(thm), theory('equality')], [c_384, c_114, c_1897])).
% 4.64/1.87  tff(c_34, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.64/1.87  tff(c_245, plain, (![A_107, B_108]: (k1_enumset1(A_107, A_107, B_108)=k2_tarski(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.64/1.87  tff(c_157, plain, (![E_74, A_75, C_76]: (r2_hidden(E_74, k1_enumset1(A_75, E_74, C_76)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.64/1.87  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.64/1.87  tff(c_161, plain, (![A_75, E_74, C_76]: (~v1_xboole_0(k1_enumset1(A_75, E_74, C_76)))), inference(resolution, [status(thm)], [c_157, c_2])).
% 4.64/1.87  tff(c_268, plain, (![A_107, B_108]: (~v1_xboole_0(k2_tarski(A_107, B_108)))), inference(superposition, [status(thm), theory('equality')], [c_245, c_161])).
% 4.64/1.87  tff(c_62, plain, (![A_29, B_30]: (r2_hidden(A_29, B_30) | v1_xboole_0(B_30) | ~m1_subset_1(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.64/1.87  tff(c_36, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.64/1.87  tff(c_647, plain, (![E_182, C_183, B_184, A_185]: (E_182=C_183 | E_182=B_184 | E_182=A_185 | ~r2_hidden(E_182, k1_enumset1(A_185, B_184, C_183)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.64/1.87  tff(c_1353, plain, (![E_248, B_249, A_250]: (E_248=B_249 | E_248=A_250 | E_248=A_250 | ~r2_hidden(E_248, k2_tarski(A_250, B_249)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_647])).
% 4.64/1.87  tff(c_1373, plain, (![B_249, A_29, A_250]: (B_249=A_29 | A_29=A_250 | v1_xboole_0(k2_tarski(A_250, B_249)) | ~m1_subset_1(A_29, k2_tarski(A_250, B_249)))), inference(resolution, [status(thm)], [c_62, c_1353])).
% 4.64/1.87  tff(c_1401, plain, (![B_251, A_252, A_253]: (B_251=A_252 | A_253=A_252 | ~m1_subset_1(A_252, k2_tarski(A_253, B_251)))), inference(negUnitSimplification, [status(thm)], [c_268, c_1373])).
% 4.64/1.87  tff(c_1422, plain, (![A_252, A_13]: (A_252=A_13 | A_252=A_13 | ~m1_subset_1(A_252, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1401])).
% 4.64/1.87  tff(c_2351, plain, (![B_311, A_312]: (k1_funct_1('#skF_12', B_311)=A_312 | ~r2_hidden(B_311, '#skF_9') | ~v5_relat_1('#skF_12', k1_tarski(A_312)))), inference(resolution, [status(thm)], [c_2016, c_1422])).
% 4.64/1.87  tff(c_2390, plain, (![A_313]: (k1_funct_1('#skF_12', '#skF_11')=A_313 | ~v5_relat_1('#skF_12', k1_tarski(A_313)))), inference(resolution, [status(thm)], [c_108, c_2351])).
% 4.64/1.87  tff(c_2396, plain, (k1_funct_1('#skF_12', '#skF_11')='#skF_10'), inference(resolution, [status(thm)], [c_526, c_2390])).
% 4.64/1.87  tff(c_2401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_2396])).
% 4.64/1.87  tff(c_2402, plain, (k1_tarski('#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1881])).
% 4.64/1.87  tff(c_12, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.64/1.87  tff(c_280, plain, (![B_111, A_112]: (r2_hidden(B_111, k2_tarski(A_112, B_111)))), inference(superposition, [status(thm), theory('equality')], [c_245, c_12])).
% 4.64/1.87  tff(c_296, plain, (![A_113]: (r2_hidden(A_113, k1_tarski(A_113)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_280])).
% 4.64/1.87  tff(c_82, plain, (![B_50, A_49]: (~r1_tarski(B_50, A_49) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.64/1.87  tff(c_307, plain, (![A_113]: (~r1_tarski(k1_tarski(A_113), A_113))), inference(resolution, [status(thm)], [c_296, c_82])).
% 4.64/1.87  tff(c_2427, plain, (~r1_tarski(k1_xboole_0, '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2402, c_307])).
% 4.64/1.87  tff(c_2440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2427])).
% 4.64/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.87  
% 4.64/1.87  Inference rules
% 4.64/1.87  ----------------------
% 4.64/1.87  #Ref     : 0
% 4.64/1.87  #Sup     : 480
% 4.64/1.87  #Fact    : 2
% 4.64/1.87  #Define  : 0
% 4.64/1.87  #Split   : 11
% 4.64/1.87  #Chain   : 0
% 4.64/1.87  #Close   : 0
% 4.64/1.87  
% 4.64/1.87  Ordering : KBO
% 4.64/1.87  
% 4.64/1.87  Simplification rules
% 4.64/1.87  ----------------------
% 4.64/1.87  #Subsume      : 61
% 4.64/1.87  #Demod        : 147
% 4.64/1.87  #Tautology    : 125
% 4.64/1.87  #SimpNegUnit  : 36
% 4.64/1.87  #BackRed      : 30
% 4.64/1.87  
% 4.64/1.87  #Partial instantiations: 0
% 4.64/1.87  #Strategies tried      : 1
% 4.64/1.87  
% 4.64/1.87  Timing (in seconds)
% 4.64/1.87  ----------------------
% 4.64/1.87  Preprocessing        : 0.38
% 4.64/1.88  Parsing              : 0.19
% 4.64/1.88  CNF conversion       : 0.03
% 4.64/1.88  Main loop            : 0.70
% 4.64/1.88  Inferencing          : 0.24
% 4.64/1.88  Reduction            : 0.22
% 4.64/1.88  Demodulation         : 0.15
% 4.64/1.88  BG Simplification    : 0.04
% 4.64/1.88  Subsumption          : 0.13
% 4.64/1.88  Abstraction          : 0.04
% 4.64/1.88  MUC search           : 0.00
% 4.64/1.88  Cooper               : 0.00
% 4.64/1.88  Total                : 1.11
% 4.64/1.88  Index Insertion      : 0.00
% 4.64/1.88  Index Deletion       : 0.00
% 4.64/1.88  Index Matching       : 0.00
% 4.64/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
