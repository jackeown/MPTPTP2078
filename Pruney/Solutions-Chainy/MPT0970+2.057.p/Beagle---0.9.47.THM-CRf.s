%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:27 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 196 expanded)
%              Number of leaves         :   38 (  84 expanded)
%              Depth                    :    9
%              Number of atoms          :  129 ( 470 expanded)
%              Number of equality atoms :   30 ( 124 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_235,plain,(
    ! [A_115,B_116,C_117] :
      ( k2_relset_1(A_115,B_116,C_117) = k2_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_253,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_235])).

tff(c_62,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_255,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_62])).

tff(c_465,plain,(
    ! [A_150,B_151,C_152] :
      ( m1_subset_1(k2_relset_1(A_150,B_151,C_152),k1_zfmisc_1(B_151))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_490,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_465])).

tff(c_499,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_490])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_580,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_499,c_16])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_587,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_580,c_8])).

tff(c_592,plain,(
    ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_587])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_328,plain,(
    ! [A_130,B_131,C_132] :
      ( k1_relset_1(A_130,B_131,C_132) = k1_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_346,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_328])).

tff(c_2422,plain,(
    ! [B_284,A_285,C_286] :
      ( k1_xboole_0 = B_284
      | k1_relset_1(A_285,B_284,C_286) = A_285
      | ~ v1_funct_2(C_286,A_285,B_284)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_285,B_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2445,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_2422])).

tff(c_2457,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_346,c_2445])).

tff(c_2503,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2457])).

tff(c_72,plain,(
    ! [D_74] :
      ( r2_hidden('#skF_9'(D_74),'#skF_6')
      | ~ r2_hidden(D_74,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_177,plain,(
    ! [C_99,B_100,A_101] :
      ( r2_hidden(C_99,B_100)
      | ~ r2_hidden(C_99,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_183,plain,(
    ! [D_74,B_100] :
      ( r2_hidden('#skF_9'(D_74),B_100)
      | ~ r1_tarski('#skF_6',B_100)
      | ~ r2_hidden(D_74,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_177])).

tff(c_24,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_105,plain,(
    ! [B_88,A_89] :
      ( v1_relat_1(B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_89))
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_111,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_64,c_105])).

tff(c_118,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_111])).

tff(c_68,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_70,plain,(
    ! [D_74] :
      ( k1_funct_1('#skF_8','#skF_9'(D_74)) = D_74
      | ~ r2_hidden(D_74,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1677,plain,(
    ! [A_231,D_232] :
      ( r2_hidden(k1_funct_1(A_231,D_232),k2_relat_1(A_231))
      | ~ r2_hidden(D_232,k1_relat_1(A_231))
      | ~ v1_funct_1(A_231)
      | ~ v1_relat_1(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1687,plain,(
    ! [D_74] :
      ( r2_hidden(D_74,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_74),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_74,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1677])).

tff(c_1708,plain,(
    ! [D_235] :
      ( r2_hidden(D_235,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_235),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_235,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_68,c_1687])).

tff(c_1713,plain,(
    ! [D_74] :
      ( r2_hidden(D_74,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_74,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_183,c_1708])).

tff(c_1776,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1713])).

tff(c_2505,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2503,c_1776])).

tff(c_2510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2505])).

tff(c_2511,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2457])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_90,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,B_84)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_98,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_14,c_90])).

tff(c_2577,plain,(
    ! [A_8] : r1_tarski('#skF_7',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2511,c_98])).

tff(c_2587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2577,c_592])).

tff(c_2644,plain,(
    ! [D_293] :
      ( r2_hidden(D_293,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_293,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1713])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2762,plain,(
    ! [A_303] :
      ( r1_tarski(A_303,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_303,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2644,c_4])).

tff(c_2770,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_2762])).

tff(c_2775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_592,c_592,c_2770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:38:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.84  
% 4.61/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.84  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 4.61/1.84  
% 4.61/1.84  %Foreground sorts:
% 4.61/1.84  
% 4.61/1.84  
% 4.61/1.84  %Background operators:
% 4.61/1.84  
% 4.61/1.84  
% 4.61/1.84  %Foreground operators:
% 4.61/1.84  tff('#skF_9', type, '#skF_9': $i > $i).
% 4.61/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.61/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.61/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/1.84  tff('#skF_7', type, '#skF_7': $i).
% 4.61/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.61/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.61/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.61/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.61/1.84  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.61/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.61/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.61/1.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.61/1.84  tff('#skF_8', type, '#skF_8': $i).
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.61/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.61/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.61/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.61/1.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.61/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.61/1.84  
% 4.78/1.85  tff(f_123, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 4.78/1.85  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.78/1.85  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.78/1.85  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.78/1.85  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.78/1.85  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.78/1.85  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.78/1.85  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.78/1.85  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.78/1.85  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.78/1.85  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.78/1.85  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.78/1.85  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.78/1.85  tff(c_235, plain, (![A_115, B_116, C_117]: (k2_relset_1(A_115, B_116, C_117)=k2_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.78/1.85  tff(c_253, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_235])).
% 4.78/1.85  tff(c_62, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.78/1.85  tff(c_255, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_253, c_62])).
% 4.78/1.85  tff(c_465, plain, (![A_150, B_151, C_152]: (m1_subset_1(k2_relset_1(A_150, B_151, C_152), k1_zfmisc_1(B_151)) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.78/1.85  tff(c_490, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_253, c_465])).
% 4.78/1.85  tff(c_499, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_490])).
% 4.78/1.85  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.78/1.85  tff(c_580, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_499, c_16])).
% 4.78/1.85  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.78/1.85  tff(c_587, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_580, c_8])).
% 4.78/1.85  tff(c_592, plain, (~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_255, c_587])).
% 4.78/1.85  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.78/1.85  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.78/1.85  tff(c_66, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.78/1.85  tff(c_328, plain, (![A_130, B_131, C_132]: (k1_relset_1(A_130, B_131, C_132)=k1_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.78/1.85  tff(c_346, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_328])).
% 4.78/1.85  tff(c_2422, plain, (![B_284, A_285, C_286]: (k1_xboole_0=B_284 | k1_relset_1(A_285, B_284, C_286)=A_285 | ~v1_funct_2(C_286, A_285, B_284) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.78/1.85  tff(c_2445, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_2422])).
% 4.78/1.85  tff(c_2457, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_346, c_2445])).
% 4.78/1.85  tff(c_2503, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_2457])).
% 4.78/1.85  tff(c_72, plain, (![D_74]: (r2_hidden('#skF_9'(D_74), '#skF_6') | ~r2_hidden(D_74, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.78/1.85  tff(c_177, plain, (![C_99, B_100, A_101]: (r2_hidden(C_99, B_100) | ~r2_hidden(C_99, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.78/1.85  tff(c_183, plain, (![D_74, B_100]: (r2_hidden('#skF_9'(D_74), B_100) | ~r1_tarski('#skF_6', B_100) | ~r2_hidden(D_74, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_177])).
% 4.78/1.85  tff(c_24, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.78/1.85  tff(c_105, plain, (![B_88, A_89]: (v1_relat_1(B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_89)) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.78/1.85  tff(c_111, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_105])).
% 4.78/1.85  tff(c_118, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_111])).
% 4.78/1.85  tff(c_68, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.78/1.85  tff(c_70, plain, (![D_74]: (k1_funct_1('#skF_8', '#skF_9'(D_74))=D_74 | ~r2_hidden(D_74, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.78/1.85  tff(c_1677, plain, (![A_231, D_232]: (r2_hidden(k1_funct_1(A_231, D_232), k2_relat_1(A_231)) | ~r2_hidden(D_232, k1_relat_1(A_231)) | ~v1_funct_1(A_231) | ~v1_relat_1(A_231))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.78/1.85  tff(c_1687, plain, (![D_74]: (r2_hidden(D_74, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_74), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_74, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1677])).
% 4.78/1.85  tff(c_1708, plain, (![D_235]: (r2_hidden(D_235, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_235), k1_relat_1('#skF_8')) | ~r2_hidden(D_235, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_68, c_1687])).
% 4.78/1.85  tff(c_1713, plain, (![D_74]: (r2_hidden(D_74, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_74, '#skF_7'))), inference(resolution, [status(thm)], [c_183, c_1708])).
% 4.78/1.85  tff(c_1776, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_1713])).
% 4.78/1.85  tff(c_2505, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2503, c_1776])).
% 4.78/1.85  tff(c_2510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2505])).
% 4.78/1.85  tff(c_2511, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2457])).
% 4.78/1.85  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.78/1.85  tff(c_90, plain, (![A_83, B_84]: (r1_tarski(A_83, B_84) | ~m1_subset_1(A_83, k1_zfmisc_1(B_84)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.78/1.85  tff(c_98, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_14, c_90])).
% 4.78/1.85  tff(c_2577, plain, (![A_8]: (r1_tarski('#skF_7', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_2511, c_98])).
% 4.78/1.85  tff(c_2587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2577, c_592])).
% 4.78/1.85  tff(c_2644, plain, (![D_293]: (r2_hidden(D_293, k2_relat_1('#skF_8')) | ~r2_hidden(D_293, '#skF_7'))), inference(splitRight, [status(thm)], [c_1713])).
% 4.78/1.85  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.78/1.85  tff(c_2762, plain, (![A_303]: (r1_tarski(A_303, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_303, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_2644, c_4])).
% 4.78/1.85  tff(c_2770, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_2762])).
% 4.78/1.85  tff(c_2775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_592, c_592, c_2770])).
% 4.78/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.85  
% 4.78/1.85  Inference rules
% 4.78/1.85  ----------------------
% 4.78/1.85  #Ref     : 0
% 4.78/1.85  #Sup     : 558
% 4.78/1.85  #Fact    : 0
% 4.78/1.85  #Define  : 0
% 4.78/1.85  #Split   : 36
% 4.78/1.85  #Chain   : 0
% 4.78/1.85  #Close   : 0
% 4.78/1.86  
% 4.78/1.86  Ordering : KBO
% 4.78/1.86  
% 4.78/1.86  Simplification rules
% 4.78/1.86  ----------------------
% 4.78/1.86  #Subsume      : 76
% 4.78/1.86  #Demod        : 373
% 4.78/1.86  #Tautology    : 160
% 4.78/1.86  #SimpNegUnit  : 27
% 4.78/1.86  #BackRed      : 93
% 4.78/1.86  
% 4.78/1.86  #Partial instantiations: 0
% 4.78/1.86  #Strategies tried      : 1
% 4.78/1.86  
% 4.78/1.86  Timing (in seconds)
% 4.78/1.86  ----------------------
% 4.78/1.86  Preprocessing        : 0.36
% 4.78/1.86  Parsing              : 0.18
% 4.78/1.86  CNF conversion       : 0.03
% 4.78/1.86  Main loop            : 0.75
% 4.78/1.86  Inferencing          : 0.24
% 4.78/1.86  Reduction            : 0.24
% 4.78/1.86  Demodulation         : 0.16
% 4.78/1.86  BG Simplification    : 0.04
% 4.78/1.86  Subsumption          : 0.17
% 4.78/1.86  Abstraction          : 0.04
% 4.78/1.86  MUC search           : 0.00
% 4.78/1.86  Cooper               : 0.00
% 4.78/1.86  Total                : 1.14
% 4.78/1.86  Index Insertion      : 0.00
% 4.78/1.86  Index Deletion       : 0.00
% 4.78/1.86  Index Matching       : 0.00
% 4.78/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
