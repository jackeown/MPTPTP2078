%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:13 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 122 expanded)
%              Number of leaves         :   45 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 220 expanded)
%              Number of equality atoms :   39 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    k1_funct_1('#skF_11','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_76,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_80,plain,(
    v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_78,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_299,plain,(
    ! [A_120,B_121,C_122] :
      ( k1_relset_1(A_120,B_121,C_122) = k1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_303,plain,(
    k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_78,c_299])).

tff(c_1163,plain,(
    ! [B_251,A_252,C_253] :
      ( k1_xboole_0 = B_251
      | k1_relset_1(A_252,B_251,C_253) = A_252
      | ~ v1_funct_2(C_253,A_252,B_251)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_252,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1170,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_78,c_1163])).

tff(c_1174,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_303,c_1170])).

tff(c_1175,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1174])).

tff(c_137,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_141,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_78,c_137])).

tff(c_82,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_751,plain,(
    ! [A_178,D_179] :
      ( r2_hidden(k1_funct_1(A_178,D_179),k2_relat_1(A_178))
      | ~ r2_hidden(D_179,k1_relat_1(A_178))
      | ~ v1_funct_1(A_178)
      | ~ v1_relat_1(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_289,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_293,plain,(
    k2_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_78,c_289])).

tff(c_308,plain,(
    ! [A_123,B_124,C_125] :
      ( m1_subset_1(k2_relset_1(A_123,B_124,C_125),k1_zfmisc_1(B_124))
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_325,plain,
    ( m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1(k1_tarski('#skF_9')))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_308])).

tff(c_331,plain,(
    m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1(k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_325])).

tff(c_34,plain,(
    ! [A_19,C_21,B_20] :
      ( m1_subset_1(A_19,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(C_21))
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_334,plain,(
    ! [A_19] :
      ( m1_subset_1(A_19,k1_tarski('#skF_9'))
      | ~ r2_hidden(A_19,k2_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_331,c_34])).

tff(c_755,plain,(
    ! [D_179] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_179),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_179,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_751,c_334])).

tff(c_772,plain,(
    ! [D_180] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_180),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_180,k1_relat_1('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_82,c_755])).

tff(c_84,plain,(
    ! [A_79] : k2_tarski(A_79,A_79) = k1_tarski(A_79) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [D_10,A_5] : r2_hidden(D_10,k2_tarski(A_5,D_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    ! [A_79] : r2_hidden(A_79,k1_tarski(A_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_10])).

tff(c_97,plain,(
    ! [B_81,A_82] :
      ( ~ r2_hidden(B_81,A_82)
      | ~ v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_79] : ~ v1_xboole_0(k1_tarski(A_79)) ),
    inference(resolution,[status(thm)],[c_90,c_97])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_156,plain,(
    ! [D_99,B_100,A_101] :
      ( D_99 = B_100
      | D_99 = A_101
      | ~ r2_hidden(D_99,k2_tarski(A_101,B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,(
    ! [D_102,A_103] :
      ( D_102 = A_103
      | D_102 = A_103
      | ~ r2_hidden(D_102,k1_tarski(A_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_156])).

tff(c_188,plain,(
    ! [A_17,A_103] :
      ( A_17 = A_103
      | v1_xboole_0(k1_tarski(A_103))
      | ~ m1_subset_1(A_17,k1_tarski(A_103)) ) ),
    inference(resolution,[status(thm)],[c_32,c_184])).

tff(c_198,plain,(
    ! [A_17,A_103] :
      ( A_17 = A_103
      | ~ m1_subset_1(A_17,k1_tarski(A_103)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_188])).

tff(c_776,plain,(
    ! [D_180] :
      ( k1_funct_1('#skF_11',D_180) = '#skF_9'
      | ~ r2_hidden(D_180,k1_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_772,c_198])).

tff(c_1261,plain,(
    ! [D_256] :
      ( k1_funct_1('#skF_11',D_256) = '#skF_9'
      | ~ r2_hidden(D_256,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_776])).

tff(c_1278,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_76,c_1261])).

tff(c_1289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1278])).

tff(c_1290,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1174])).

tff(c_1314,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1290,c_107])).

tff(c_1322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:53:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.59  
% 3.60/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.59  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.60/1.59  
% 3.60/1.59  %Foreground sorts:
% 3.60/1.59  
% 3.60/1.59  
% 3.60/1.59  %Background operators:
% 3.60/1.59  
% 3.60/1.59  
% 3.60/1.59  %Foreground operators:
% 3.60/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.60/1.59  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.60/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.60/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.60/1.59  tff('#skF_11', type, '#skF_11': $i).
% 3.60/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.60/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.60/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.60/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.60/1.59  tff('#skF_10', type, '#skF_10': $i).
% 3.60/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.60/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.60/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.60/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.60/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.60/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.60/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.60/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.59  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.60/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.60/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.60/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.60/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.60/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.60/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.60/1.59  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.60/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.60/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.60/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.59  
% 3.60/1.61  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.60/1.61  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.60/1.61  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.60/1.61  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.60/1.61  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.60/1.61  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.60/1.61  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.60/1.61  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.60/1.61  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.60/1.61  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.60/1.61  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.60/1.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.60/1.61  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.60/1.61  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.60/1.61  tff(c_74, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.60/1.61  tff(c_76, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.60/1.61  tff(c_80, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.60/1.61  tff(c_78, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.60/1.61  tff(c_299, plain, (![A_120, B_121, C_122]: (k1_relset_1(A_120, B_121, C_122)=k1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.60/1.61  tff(c_303, plain, (k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_78, c_299])).
% 3.60/1.61  tff(c_1163, plain, (![B_251, A_252, C_253]: (k1_xboole_0=B_251 | k1_relset_1(A_252, B_251, C_253)=A_252 | ~v1_funct_2(C_253, A_252, B_251) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_252, B_251))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.60/1.61  tff(c_1170, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_78, c_1163])).
% 3.60/1.61  tff(c_1174, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_303, c_1170])).
% 3.60/1.61  tff(c_1175, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_1174])).
% 3.60/1.61  tff(c_137, plain, (![C_91, A_92, B_93]: (v1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.60/1.61  tff(c_141, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_78, c_137])).
% 3.60/1.61  tff(c_82, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.60/1.61  tff(c_751, plain, (![A_178, D_179]: (r2_hidden(k1_funct_1(A_178, D_179), k2_relat_1(A_178)) | ~r2_hidden(D_179, k1_relat_1(A_178)) | ~v1_funct_1(A_178) | ~v1_relat_1(A_178))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.60/1.61  tff(c_289, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.60/1.61  tff(c_293, plain, (k2_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_78, c_289])).
% 3.60/1.61  tff(c_308, plain, (![A_123, B_124, C_125]: (m1_subset_1(k2_relset_1(A_123, B_124, C_125), k1_zfmisc_1(B_124)) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.60/1.61  tff(c_325, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1(k1_tarski('#skF_9'))) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_293, c_308])).
% 3.60/1.61  tff(c_331, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1(k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_325])).
% 3.60/1.61  tff(c_34, plain, (![A_19, C_21, B_20]: (m1_subset_1(A_19, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(C_21)) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.60/1.61  tff(c_334, plain, (![A_19]: (m1_subset_1(A_19, k1_tarski('#skF_9')) | ~r2_hidden(A_19, k2_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_331, c_34])).
% 3.60/1.61  tff(c_755, plain, (![D_179]: (m1_subset_1(k1_funct_1('#skF_11', D_179), k1_tarski('#skF_9')) | ~r2_hidden(D_179, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_751, c_334])).
% 3.60/1.61  tff(c_772, plain, (![D_180]: (m1_subset_1(k1_funct_1('#skF_11', D_180), k1_tarski('#skF_9')) | ~r2_hidden(D_180, k1_relat_1('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_82, c_755])).
% 3.60/1.61  tff(c_84, plain, (![A_79]: (k2_tarski(A_79, A_79)=k1_tarski(A_79))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.60/1.61  tff(c_10, plain, (![D_10, A_5]: (r2_hidden(D_10, k2_tarski(A_5, D_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.60/1.61  tff(c_90, plain, (![A_79]: (r2_hidden(A_79, k1_tarski(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_10])).
% 3.60/1.61  tff(c_97, plain, (![B_81, A_82]: (~r2_hidden(B_81, A_82) | ~v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.60/1.61  tff(c_107, plain, (![A_79]: (~v1_xboole_0(k1_tarski(A_79)))), inference(resolution, [status(thm)], [c_90, c_97])).
% 3.60/1.61  tff(c_32, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | v1_xboole_0(B_18) | ~m1_subset_1(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.60/1.61  tff(c_26, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.60/1.61  tff(c_156, plain, (![D_99, B_100, A_101]: (D_99=B_100 | D_99=A_101 | ~r2_hidden(D_99, k2_tarski(A_101, B_100)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.60/1.61  tff(c_184, plain, (![D_102, A_103]: (D_102=A_103 | D_102=A_103 | ~r2_hidden(D_102, k1_tarski(A_103)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_156])).
% 3.60/1.61  tff(c_188, plain, (![A_17, A_103]: (A_17=A_103 | v1_xboole_0(k1_tarski(A_103)) | ~m1_subset_1(A_17, k1_tarski(A_103)))), inference(resolution, [status(thm)], [c_32, c_184])).
% 3.60/1.61  tff(c_198, plain, (![A_17, A_103]: (A_17=A_103 | ~m1_subset_1(A_17, k1_tarski(A_103)))), inference(negUnitSimplification, [status(thm)], [c_107, c_188])).
% 3.60/1.61  tff(c_776, plain, (![D_180]: (k1_funct_1('#skF_11', D_180)='#skF_9' | ~r2_hidden(D_180, k1_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_772, c_198])).
% 3.60/1.61  tff(c_1261, plain, (![D_256]: (k1_funct_1('#skF_11', D_256)='#skF_9' | ~r2_hidden(D_256, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_776])).
% 3.60/1.61  tff(c_1278, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_76, c_1261])).
% 3.60/1.61  tff(c_1289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1278])).
% 3.60/1.61  tff(c_1290, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1174])).
% 3.60/1.61  tff(c_1314, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1290, c_107])).
% 3.60/1.61  tff(c_1322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1314])).
% 3.60/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.61  
% 3.60/1.61  Inference rules
% 3.60/1.61  ----------------------
% 3.60/1.61  #Ref     : 0
% 3.60/1.61  #Sup     : 242
% 3.60/1.61  #Fact    : 2
% 3.60/1.61  #Define  : 0
% 3.60/1.61  #Split   : 7
% 3.60/1.61  #Chain   : 0
% 3.60/1.61  #Close   : 0
% 3.60/1.61  
% 3.60/1.61  Ordering : KBO
% 3.60/1.61  
% 3.60/1.61  Simplification rules
% 3.60/1.61  ----------------------
% 3.60/1.61  #Subsume      : 45
% 3.60/1.61  #Demod        : 128
% 3.60/1.61  #Tautology    : 82
% 3.60/1.61  #SimpNegUnit  : 20
% 3.60/1.61  #BackRed      : 27
% 3.60/1.61  
% 3.60/1.61  #Partial instantiations: 0
% 3.60/1.61  #Strategies tried      : 1
% 3.60/1.61  
% 3.60/1.61  Timing (in seconds)
% 3.60/1.61  ----------------------
% 3.60/1.61  Preprocessing        : 0.37
% 3.60/1.61  Parsing              : 0.18
% 3.60/1.61  CNF conversion       : 0.03
% 3.60/1.61  Main loop            : 0.47
% 3.60/1.61  Inferencing          : 0.18
% 3.60/1.61  Reduction            : 0.14
% 3.60/1.61  Demodulation         : 0.10
% 3.60/1.61  BG Simplification    : 0.03
% 3.60/1.61  Subsumption          : 0.09
% 3.60/1.61  Abstraction          : 0.03
% 3.60/1.61  MUC search           : 0.00
% 3.60/1.61  Cooper               : 0.00
% 3.60/1.61  Total                : 0.87
% 3.60/1.61  Index Insertion      : 0.00
% 3.60/1.61  Index Deletion       : 0.00
% 3.60/1.61  Index Matching       : 0.00
% 3.60/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
