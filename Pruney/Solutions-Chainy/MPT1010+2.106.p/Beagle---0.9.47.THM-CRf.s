%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:19 EST 2020

% Result     : Theorem 5.53s
% Output     : CNFRefutation 5.53s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 111 expanded)
%              Number of leaves         :   44 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 203 expanded)
%              Number of equality atoms :   35 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

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
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_73,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_74,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_32,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_137,plain,(
    ! [B_95,A_96] :
      ( v1_relat_1(B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_96))
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_140,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_76,c_137])).

tff(c_143,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_140])).

tff(c_80,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_78,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_188,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_192,plain,(
    k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_188])).

tff(c_305,plain,(
    ! [B_155,A_156,C_157] :
      ( k1_xboole_0 = B_155
      | k1_relset_1(A_156,B_155,C_157) = A_156
      | ~ v1_funct_2(C_157,A_156,B_155)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_312,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_76,c_305])).

tff(c_316,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_192,c_312])).

tff(c_317,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_206,plain,(
    ! [A_121,B_122,C_123] :
      ( k2_relset_1(A_121,B_122,C_123) = k2_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_210,plain,(
    k2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_206])).

tff(c_215,plain,(
    ! [A_124,B_125,C_126] :
      ( m1_subset_1(k2_relset_1(A_124,B_125,C_126),k1_zfmisc_1(B_125))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_229,plain,
    ( m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_215])).

tff(c_234,plain,(
    m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_229])).

tff(c_257,plain,(
    ! [A_132,D_133] :
      ( r2_hidden(k1_funct_1(A_132,D_133),k2_relat_1(A_132))
      | ~ r2_hidden(D_133,k1_relat_1(A_132))
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [C_17,A_14,B_15] :
      ( r2_hidden(C_17,A_14)
      | ~ r2_hidden(C_17,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4876,plain,(
    ! [A_13769,D_13770,A_13771] :
      ( r2_hidden(k1_funct_1(A_13769,D_13770),A_13771)
      | ~ m1_subset_1(k2_relat_1(A_13769),k1_zfmisc_1(A_13771))
      | ~ r2_hidden(D_13770,k1_relat_1(A_13769))
      | ~ v1_funct_1(A_13769)
      | ~ v1_relat_1(A_13769) ) ),
    inference(resolution,[status(thm)],[c_257,c_28])).

tff(c_4884,plain,(
    ! [D_13770] :
      ( r2_hidden(k1_funct_1('#skF_10',D_13770),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_13770,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_234,c_4876])).

tff(c_4888,plain,(
    ! [D_13886] :
      ( r2_hidden(k1_funct_1('#skF_10',D_13886),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_13886,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_80,c_317,c_4884])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_144,plain,(
    ! [D_97,B_98,A_99] :
      ( D_97 = B_98
      | D_97 = A_99
      | ~ r2_hidden(D_97,k2_tarski(A_99,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_153,plain,(
    ! [D_97,A_8] :
      ( D_97 = A_8
      | D_97 = A_8
      | ~ r2_hidden(D_97,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_144])).

tff(c_4965,plain,(
    ! [D_14001] :
      ( k1_funct_1('#skF_10',D_14001) = '#skF_8'
      | ~ r2_hidden(D_14001,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4888,c_153])).

tff(c_5008,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_74,c_4965])).

tff(c_5023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5008])).

tff(c_5024,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_92,plain,(
    ! [D_81,A_82] : r2_hidden(D_81,k2_tarski(A_82,D_81)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_95,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_92])).

tff(c_102,plain,(
    ! [B_86,A_87] :
      ( ~ r1_tarski(B_86,A_87)
      | ~ r2_hidden(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_116,plain,(
    ! [A_8] : ~ r1_tarski(k1_tarski(A_8),A_8) ),
    inference(resolution,[status(thm)],[c_95,c_102])).

tff(c_5041,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5024,c_116])).

tff(c_5049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5041])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:01:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.53/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.53/2.13  
% 5.53/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.53/2.14  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 5.53/2.14  
% 5.53/2.14  %Foreground sorts:
% 5.53/2.14  
% 5.53/2.14  
% 5.53/2.14  %Background operators:
% 5.53/2.14  
% 5.53/2.14  
% 5.53/2.14  %Foreground operators:
% 5.53/2.14  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.53/2.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.53/2.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.53/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.53/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.53/2.14  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.53/2.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.53/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.53/2.14  tff('#skF_7', type, '#skF_7': $i).
% 5.53/2.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.53/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.53/2.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.53/2.14  tff('#skF_10', type, '#skF_10': $i).
% 5.53/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.53/2.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.53/2.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.53/2.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.53/2.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.53/2.14  tff('#skF_9', type, '#skF_9': $i).
% 5.53/2.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.53/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.53/2.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.53/2.14  tff('#skF_8', type, '#skF_8': $i).
% 5.53/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.53/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.53/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.53/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.53/2.14  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.53/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.53/2.14  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.53/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.53/2.14  
% 5.53/2.15  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.53/2.15  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 5.53/2.15  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.53/2.15  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.53/2.15  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.53/2.15  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.53/2.15  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.53/2.15  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.53/2.15  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 5.53/2.15  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.53/2.15  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.53/2.15  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.53/2.15  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.53/2.15  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.53/2.15  tff(c_72, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.53/2.15  tff(c_74, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.53/2.15  tff(c_32, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.53/2.15  tff(c_76, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.53/2.15  tff(c_137, plain, (![B_95, A_96]: (v1_relat_1(B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_96)) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.53/2.15  tff(c_140, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_76, c_137])).
% 5.53/2.15  tff(c_143, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_140])).
% 5.53/2.15  tff(c_80, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.53/2.15  tff(c_78, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.53/2.15  tff(c_188, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.53/2.15  tff(c_192, plain, (k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_188])).
% 5.53/2.15  tff(c_305, plain, (![B_155, A_156, C_157]: (k1_xboole_0=B_155 | k1_relset_1(A_156, B_155, C_157)=A_156 | ~v1_funct_2(C_157, A_156, B_155) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.53/2.15  tff(c_312, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_76, c_305])).
% 5.53/2.15  tff(c_316, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_192, c_312])).
% 5.53/2.15  tff(c_317, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_316])).
% 5.53/2.15  tff(c_206, plain, (![A_121, B_122, C_123]: (k2_relset_1(A_121, B_122, C_123)=k2_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.53/2.15  tff(c_210, plain, (k2_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_206])).
% 5.53/2.15  tff(c_215, plain, (![A_124, B_125, C_126]: (m1_subset_1(k2_relset_1(A_124, B_125, C_126), k1_zfmisc_1(B_125)) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.53/2.15  tff(c_229, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_210, c_215])).
% 5.53/2.15  tff(c_234, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_229])).
% 5.53/2.15  tff(c_257, plain, (![A_132, D_133]: (r2_hidden(k1_funct_1(A_132, D_133), k2_relat_1(A_132)) | ~r2_hidden(D_133, k1_relat_1(A_132)) | ~v1_funct_1(A_132) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.53/2.15  tff(c_28, plain, (![C_17, A_14, B_15]: (r2_hidden(C_17, A_14) | ~r2_hidden(C_17, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.53/2.15  tff(c_4876, plain, (![A_13769, D_13770, A_13771]: (r2_hidden(k1_funct_1(A_13769, D_13770), A_13771) | ~m1_subset_1(k2_relat_1(A_13769), k1_zfmisc_1(A_13771)) | ~r2_hidden(D_13770, k1_relat_1(A_13769)) | ~v1_funct_1(A_13769) | ~v1_relat_1(A_13769))), inference(resolution, [status(thm)], [c_257, c_28])).
% 5.53/2.15  tff(c_4884, plain, (![D_13770]: (r2_hidden(k1_funct_1('#skF_10', D_13770), k1_tarski('#skF_8')) | ~r2_hidden(D_13770, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_234, c_4876])).
% 5.53/2.15  tff(c_4888, plain, (![D_13886]: (r2_hidden(k1_funct_1('#skF_10', D_13886), k1_tarski('#skF_8')) | ~r2_hidden(D_13886, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_80, c_317, c_4884])).
% 5.53/2.15  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.53/2.15  tff(c_144, plain, (![D_97, B_98, A_99]: (D_97=B_98 | D_97=A_99 | ~r2_hidden(D_97, k2_tarski(A_99, B_98)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.53/2.15  tff(c_153, plain, (![D_97, A_8]: (D_97=A_8 | D_97=A_8 | ~r2_hidden(D_97, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_144])).
% 5.53/2.15  tff(c_4965, plain, (![D_14001]: (k1_funct_1('#skF_10', D_14001)='#skF_8' | ~r2_hidden(D_14001, '#skF_7'))), inference(resolution, [status(thm)], [c_4888, c_153])).
% 5.53/2.15  tff(c_5008, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_74, c_4965])).
% 5.53/2.15  tff(c_5023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_5008])).
% 5.53/2.15  tff(c_5024, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_316])).
% 5.53/2.15  tff(c_92, plain, (![D_81, A_82]: (r2_hidden(D_81, k2_tarski(A_82, D_81)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.53/2.15  tff(c_95, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_92])).
% 5.53/2.15  tff(c_102, plain, (![B_86, A_87]: (~r1_tarski(B_86, A_87) | ~r2_hidden(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.53/2.15  tff(c_116, plain, (![A_8]: (~r1_tarski(k1_tarski(A_8), A_8))), inference(resolution, [status(thm)], [c_95, c_102])).
% 5.53/2.15  tff(c_5041, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5024, c_116])).
% 5.53/2.15  tff(c_5049, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_5041])).
% 5.53/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.53/2.15  
% 5.53/2.15  Inference rules
% 5.53/2.15  ----------------------
% 5.53/2.15  #Ref     : 0
% 5.53/2.15  #Sup     : 655
% 5.53/2.15  #Fact    : 10
% 5.53/2.15  #Define  : 0
% 5.53/2.15  #Split   : 10
% 5.53/2.15  #Chain   : 0
% 5.53/2.15  #Close   : 0
% 5.53/2.15  
% 5.53/2.15  Ordering : KBO
% 5.53/2.15  
% 5.53/2.15  Simplification rules
% 5.53/2.15  ----------------------
% 5.53/2.15  #Subsume      : 162
% 5.53/2.15  #Demod        : 147
% 5.53/2.15  #Tautology    : 155
% 5.53/2.15  #SimpNegUnit  : 4
% 5.53/2.15  #BackRed      : 20
% 5.53/2.15  
% 5.53/2.15  #Partial instantiations: 7986
% 5.53/2.15  #Strategies tried      : 1
% 5.53/2.15  
% 5.53/2.15  Timing (in seconds)
% 5.53/2.15  ----------------------
% 5.67/2.15  Preprocessing        : 0.34
% 5.67/2.15  Parsing              : 0.17
% 5.67/2.15  CNF conversion       : 0.03
% 5.67/2.15  Main loop            : 0.96
% 5.67/2.15  Inferencing          : 0.48
% 5.67/2.15  Reduction            : 0.22
% 5.67/2.15  Demodulation         : 0.15
% 5.67/2.15  BG Simplification    : 0.04
% 5.67/2.15  Subsumption          : 0.16
% 5.67/2.15  Abstraction          : 0.05
% 5.67/2.15  MUC search           : 0.00
% 5.67/2.15  Cooper               : 0.00
% 5.67/2.15  Total                : 1.34
% 5.67/2.15  Index Insertion      : 0.00
% 5.67/2.15  Index Deletion       : 0.00
% 5.67/2.16  Index Matching       : 0.00
% 5.67/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
