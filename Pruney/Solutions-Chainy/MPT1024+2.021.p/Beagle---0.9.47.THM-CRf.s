%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:24 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 142 expanded)
%              Number of leaves         :   38 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  135 ( 341 expanded)
%              Number of equality atoms :   29 (  72 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_113,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
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

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_108,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_1'(A_91,B_92),A_91)
      | r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [A_91] : r1_tarski(A_91,A_91) ),
    inference(resolution,[status(thm)],[c_108,c_4])).

tff(c_64,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_86,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_95,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_86])).

tff(c_68,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16,plain,(
    ! [A_9,B_32,D_47] :
      ( k1_funct_1(A_9,'#skF_5'(A_9,B_32,k9_relat_1(A_9,B_32),D_47)) = D_47
      | ~ r2_hidden(D_47,k9_relat_1(A_9,B_32))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_9,B_32,D_47] :
      ( r2_hidden('#skF_5'(A_9,B_32,k9_relat_1(A_9,B_32),D_47),B_32)
      | ~ r2_hidden(D_47,k9_relat_1(A_9,B_32))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_66,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_186,plain,(
    ! [A_109,B_110,C_111] :
      ( k1_relset_1(A_109,B_110,C_111) = k1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_195,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_186])).

tff(c_723,plain,(
    ! [B_203,A_204,C_205] :
      ( k1_xboole_0 = B_203
      | k1_relset_1(A_204,B_203,C_205) = A_204
      | ~ v1_funct_2(C_205,A_204,B_203)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_734,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_723])).

tff(c_739,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_195,c_734])).

tff(c_740,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_739])).

tff(c_1138,plain,(
    ! [A_273,B_274,D_275] :
      ( r2_hidden('#skF_5'(A_273,B_274,k9_relat_1(A_273,B_274),D_275),k1_relat_1(A_273))
      | ~ r2_hidden(D_275,k9_relat_1(A_273,B_274))
      | ~ v1_funct_1(A_273)
      | ~ v1_relat_1(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1146,plain,(
    ! [B_274,D_275] :
      ( r2_hidden('#skF_5'('#skF_9',B_274,k9_relat_1('#skF_9',B_274),D_275),'#skF_6')
      | ~ r2_hidden(D_275,k9_relat_1('#skF_9',B_274))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_1138])).

tff(c_1211,plain,(
    ! [B_286,D_287] :
      ( r2_hidden('#skF_5'('#skF_9',B_286,k9_relat_1('#skF_9',B_286),D_287),'#skF_6')
      | ~ r2_hidden(D_287,k9_relat_1('#skF_9',B_286)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_68,c_1146])).

tff(c_60,plain,(
    ! [F_74] :
      ( k1_funct_1('#skF_9',F_74) != '#skF_10'
      | ~ r2_hidden(F_74,'#skF_8')
      | ~ r2_hidden(F_74,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1356,plain,(
    ! [B_319,D_320] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_319,k9_relat_1('#skF_9',B_319),D_320)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_319,k9_relat_1('#skF_9',B_319),D_320),'#skF_8')
      | ~ r2_hidden(D_320,k9_relat_1('#skF_9',B_319)) ) ),
    inference(resolution,[status(thm)],[c_1211,c_60])).

tff(c_1360,plain,(
    ! [D_47] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_47)) != '#skF_10'
      | ~ r2_hidden(D_47,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18,c_1356])).

tff(c_1829,plain,(
    ! [D_379] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_379)) != '#skF_10'
      | ~ r2_hidden(D_379,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_68,c_1360])).

tff(c_1833,plain,(
    ! [D_47] :
      ( D_47 != '#skF_10'
      | ~ r2_hidden(D_47,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_47,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1829])).

tff(c_1836,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_68,c_1833])).

tff(c_284,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k7_relset_1(A_132,B_133,C_134,D_135) = k9_relat_1(C_134,D_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_291,plain,(
    ! [D_135] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_135) = k9_relat_1('#skF_9',D_135) ),
    inference(resolution,[status(thm)],[c_64,c_284])).

tff(c_62,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_294,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_62])).

tff(c_1838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1836,c_294])).

tff(c_1839,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_739])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_304,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( m1_subset_1(k7_relset_1(A_137,B_138,C_139,D_140),k1_zfmisc_1(B_138))
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_325,plain,(
    ! [D_135] :
      ( m1_subset_1(k9_relat_1('#skF_9',D_135),k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_304])).

tff(c_340,plain,(
    ! [D_141] : m1_subset_1(k9_relat_1('#skF_9',D_141),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_325])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_344,plain,(
    ! [D_141] : r1_tarski(k9_relat_1('#skF_9',D_141),'#skF_7') ),
    inference(resolution,[status(thm)],[c_340,c_10])).

tff(c_138,plain,(
    ! [C_99,B_100,A_101] :
      ( r2_hidden(C_99,B_100)
      | ~ r2_hidden(C_99,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_144,plain,(
    ! [B_100] :
      ( r2_hidden('#skF_10',B_100)
      | ~ r1_tarski(k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8'),B_100) ) ),
    inference(resolution,[status(thm)],[c_62,c_138])).

tff(c_346,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_10',B_143)
      | ~ r1_tarski(k9_relat_1('#skF_9','#skF_8'),B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_144])).

tff(c_355,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_344,c_346])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_365,plain,(
    ! [B_144] :
      ( r2_hidden('#skF_10',B_144)
      | ~ r1_tarski('#skF_7',B_144) ) ),
    inference(resolution,[status(thm)],[c_355,c_2])).

tff(c_38,plain,(
    ! [B_52,A_51] :
      ( ~ r1_tarski(B_52,A_51)
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_378,plain,(
    ! [B_145] :
      ( ~ r1_tarski(B_145,'#skF_10')
      | ~ r1_tarski('#skF_7',B_145) ) ),
    inference(resolution,[status(thm)],[c_365,c_38])).

tff(c_386,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_378])).

tff(c_1855,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1839,c_386])).

tff(c_1866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_1855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:24:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/2.23  
% 4.85/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/2.23  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 4.85/2.23  
% 4.85/2.23  %Foreground sorts:
% 4.85/2.23  
% 4.85/2.23  
% 4.85/2.23  %Background operators:
% 4.85/2.23  
% 4.85/2.23  
% 4.85/2.23  %Foreground operators:
% 4.85/2.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.85/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.85/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.85/2.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.85/2.23  tff('#skF_7', type, '#skF_7': $i).
% 4.85/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.85/2.23  tff('#skF_10', type, '#skF_10': $i).
% 4.85/2.23  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.85/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.85/2.23  tff('#skF_6', type, '#skF_6': $i).
% 4.85/2.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.85/2.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.85/2.23  tff('#skF_9', type, '#skF_9': $i).
% 4.85/2.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.85/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.85/2.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.85/2.23  tff('#skF_8', type, '#skF_8': $i).
% 4.85/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/2.23  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.85/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.85/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.85/2.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.85/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/2.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.85/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.85/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.85/2.23  
% 4.85/2.25  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.85/2.25  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 4.85/2.25  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.85/2.25  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 4.85/2.25  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.85/2.25  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.85/2.25  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.85/2.25  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.85/2.25  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.85/2.25  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.85/2.25  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.85/2.25  tff(c_108, plain, (![A_91, B_92]: (r2_hidden('#skF_1'(A_91, B_92), A_91) | r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.85/2.25  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.85/2.25  tff(c_120, plain, (![A_91]: (r1_tarski(A_91, A_91))), inference(resolution, [status(thm)], [c_108, c_4])).
% 4.85/2.25  tff(c_64, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.85/2.25  tff(c_86, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.85/2.25  tff(c_95, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_64, c_86])).
% 4.85/2.25  tff(c_68, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.85/2.25  tff(c_16, plain, (![A_9, B_32, D_47]: (k1_funct_1(A_9, '#skF_5'(A_9, B_32, k9_relat_1(A_9, B_32), D_47))=D_47 | ~r2_hidden(D_47, k9_relat_1(A_9, B_32)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.85/2.25  tff(c_18, plain, (![A_9, B_32, D_47]: (r2_hidden('#skF_5'(A_9, B_32, k9_relat_1(A_9, B_32), D_47), B_32) | ~r2_hidden(D_47, k9_relat_1(A_9, B_32)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.85/2.25  tff(c_66, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.85/2.25  tff(c_186, plain, (![A_109, B_110, C_111]: (k1_relset_1(A_109, B_110, C_111)=k1_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.85/2.25  tff(c_195, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_64, c_186])).
% 4.85/2.25  tff(c_723, plain, (![B_203, A_204, C_205]: (k1_xboole_0=B_203 | k1_relset_1(A_204, B_203, C_205)=A_204 | ~v1_funct_2(C_205, A_204, B_203) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.85/2.25  tff(c_734, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_723])).
% 4.85/2.25  tff(c_739, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_195, c_734])).
% 4.85/2.25  tff(c_740, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_739])).
% 4.85/2.25  tff(c_1138, plain, (![A_273, B_274, D_275]: (r2_hidden('#skF_5'(A_273, B_274, k9_relat_1(A_273, B_274), D_275), k1_relat_1(A_273)) | ~r2_hidden(D_275, k9_relat_1(A_273, B_274)) | ~v1_funct_1(A_273) | ~v1_relat_1(A_273))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.85/2.25  tff(c_1146, plain, (![B_274, D_275]: (r2_hidden('#skF_5'('#skF_9', B_274, k9_relat_1('#skF_9', B_274), D_275), '#skF_6') | ~r2_hidden(D_275, k9_relat_1('#skF_9', B_274)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_740, c_1138])).
% 4.85/2.25  tff(c_1211, plain, (![B_286, D_287]: (r2_hidden('#skF_5'('#skF_9', B_286, k9_relat_1('#skF_9', B_286), D_287), '#skF_6') | ~r2_hidden(D_287, k9_relat_1('#skF_9', B_286)))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_68, c_1146])).
% 4.85/2.25  tff(c_60, plain, (![F_74]: (k1_funct_1('#skF_9', F_74)!='#skF_10' | ~r2_hidden(F_74, '#skF_8') | ~r2_hidden(F_74, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.85/2.25  tff(c_1356, plain, (![B_319, D_320]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_319, k9_relat_1('#skF_9', B_319), D_320))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_319, k9_relat_1('#skF_9', B_319), D_320), '#skF_8') | ~r2_hidden(D_320, k9_relat_1('#skF_9', B_319)))), inference(resolution, [status(thm)], [c_1211, c_60])).
% 4.85/2.25  tff(c_1360, plain, (![D_47]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_47))!='#skF_10' | ~r2_hidden(D_47, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_18, c_1356])).
% 4.85/2.25  tff(c_1829, plain, (![D_379]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_379))!='#skF_10' | ~r2_hidden(D_379, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_68, c_1360])).
% 4.85/2.25  tff(c_1833, plain, (![D_47]: (D_47!='#skF_10' | ~r2_hidden(D_47, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_47, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1829])).
% 4.85/2.25  tff(c_1836, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_68, c_1833])).
% 4.85/2.25  tff(c_284, plain, (![A_132, B_133, C_134, D_135]: (k7_relset_1(A_132, B_133, C_134, D_135)=k9_relat_1(C_134, D_135) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.85/2.25  tff(c_291, plain, (![D_135]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_135)=k9_relat_1('#skF_9', D_135))), inference(resolution, [status(thm)], [c_64, c_284])).
% 4.85/2.25  tff(c_62, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.85/2.25  tff(c_294, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_62])).
% 4.85/2.25  tff(c_1838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1836, c_294])).
% 4.85/2.25  tff(c_1839, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_739])).
% 4.85/2.25  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.85/2.25  tff(c_304, plain, (![A_137, B_138, C_139, D_140]: (m1_subset_1(k7_relset_1(A_137, B_138, C_139, D_140), k1_zfmisc_1(B_138)) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.85/2.25  tff(c_325, plain, (![D_135]: (m1_subset_1(k9_relat_1('#skF_9', D_135), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_291, c_304])).
% 4.85/2.25  tff(c_340, plain, (![D_141]: (m1_subset_1(k9_relat_1('#skF_9', D_141), k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_325])).
% 4.85/2.25  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.85/2.25  tff(c_344, plain, (![D_141]: (r1_tarski(k9_relat_1('#skF_9', D_141), '#skF_7'))), inference(resolution, [status(thm)], [c_340, c_10])).
% 4.85/2.25  tff(c_138, plain, (![C_99, B_100, A_101]: (r2_hidden(C_99, B_100) | ~r2_hidden(C_99, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.85/2.25  tff(c_144, plain, (![B_100]: (r2_hidden('#skF_10', B_100) | ~r1_tarski(k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'), B_100))), inference(resolution, [status(thm)], [c_62, c_138])).
% 4.85/2.25  tff(c_346, plain, (![B_143]: (r2_hidden('#skF_10', B_143) | ~r1_tarski(k9_relat_1('#skF_9', '#skF_8'), B_143))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_144])).
% 4.85/2.25  tff(c_355, plain, (r2_hidden('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_344, c_346])).
% 4.85/2.25  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.85/2.25  tff(c_365, plain, (![B_144]: (r2_hidden('#skF_10', B_144) | ~r1_tarski('#skF_7', B_144))), inference(resolution, [status(thm)], [c_355, c_2])).
% 4.85/2.25  tff(c_38, plain, (![B_52, A_51]: (~r1_tarski(B_52, A_51) | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.85/2.25  tff(c_378, plain, (![B_145]: (~r1_tarski(B_145, '#skF_10') | ~r1_tarski('#skF_7', B_145))), inference(resolution, [status(thm)], [c_365, c_38])).
% 4.85/2.25  tff(c_386, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_378])).
% 4.85/2.25  tff(c_1855, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1839, c_386])).
% 4.85/2.25  tff(c_1866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_1855])).
% 4.85/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/2.25  
% 4.85/2.25  Inference rules
% 4.85/2.25  ----------------------
% 4.85/2.25  #Ref     : 0
% 4.85/2.25  #Sup     : 357
% 4.85/2.25  #Fact    : 0
% 4.85/2.25  #Define  : 0
% 4.85/2.25  #Split   : 5
% 4.85/2.25  #Chain   : 0
% 4.85/2.25  #Close   : 0
% 4.85/2.25  
% 4.85/2.25  Ordering : KBO
% 4.85/2.25  
% 4.85/2.25  Simplification rules
% 4.85/2.25  ----------------------
% 4.85/2.25  #Subsume      : 26
% 4.85/2.25  #Demod        : 187
% 4.85/2.25  #Tautology    : 117
% 4.85/2.25  #SimpNegUnit  : 1
% 4.85/2.25  #BackRed      : 39
% 4.85/2.25  
% 4.85/2.25  #Partial instantiations: 0
% 4.85/2.25  #Strategies tried      : 1
% 4.85/2.25  
% 4.85/2.25  Timing (in seconds)
% 4.85/2.25  ----------------------
% 4.85/2.25  Preprocessing        : 0.58
% 4.85/2.25  Parsing              : 0.29
% 4.85/2.25  CNF conversion       : 0.05
% 4.85/2.25  Main loop            : 0.82
% 4.85/2.25  Inferencing          : 0.30
% 4.85/2.25  Reduction            : 0.25
% 4.85/2.25  Demodulation         : 0.18
% 4.85/2.25  BG Simplification    : 0.05
% 4.85/2.25  Subsumption          : 0.16
% 4.85/2.25  Abstraction          : 0.05
% 4.85/2.25  MUC search           : 0.00
% 4.85/2.25  Cooper               : 0.00
% 4.85/2.25  Total                : 1.45
% 4.85/2.25  Index Insertion      : 0.00
% 4.85/2.25  Index Deletion       : 0.00
% 4.85/2.25  Index Matching       : 0.00
% 4.85/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
