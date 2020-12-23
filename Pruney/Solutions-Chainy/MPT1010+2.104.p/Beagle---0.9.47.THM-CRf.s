%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:19 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 116 expanded)
%              Number of leaves         :   44 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  123 ( 216 expanded)
%              Number of equality atoms :   44 (  77 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

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

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_77,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_78,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_80,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_156,plain,(
    ! [B_102,A_103] :
      ( v1_relat_1(B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_103))
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_159,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_80,c_156])).

tff(c_162,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_159])).

tff(c_84,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_82,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_277,plain,(
    ! [A_149,B_150,C_151] :
      ( k1_relset_1(A_149,B_150,C_151) = k1_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_281,plain,(
    k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_80,c_277])).

tff(c_386,plain,(
    ! [B_180,A_181,C_182] :
      ( k1_xboole_0 = B_180
      | k1_relset_1(A_181,B_180,C_182) = A_181
      | ~ v1_funct_2(C_182,A_181,B_180)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_181,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_393,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_80,c_386])).

tff(c_397,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_281,c_393])).

tff(c_398,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_268,plain,(
    ! [A_146,B_147,C_148] :
      ( k2_relset_1(A_146,B_147,C_148) = k2_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_272,plain,(
    k2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_80,c_268])).

tff(c_287,plain,(
    ! [A_153,B_154,C_155] :
      ( m1_subset_1(k2_relset_1(A_153,B_154,C_155),k1_zfmisc_1(B_154))
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_301,plain,
    ( m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_287])).

tff(c_306,plain,(
    m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_301])).

tff(c_307,plain,(
    ! [A_156,D_157] :
      ( r2_hidden(k1_funct_1(A_156,D_157),k2_relat_1(A_156))
      | ~ r2_hidden(D_157,k1_relat_1(A_156))
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(C_15,A_12)
      | ~ r2_hidden(C_15,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_792,plain,(
    ! [A_241,D_242,A_243] :
      ( r2_hidden(k1_funct_1(A_241,D_242),A_243)
      | ~ m1_subset_1(k2_relat_1(A_241),k1_zfmisc_1(A_243))
      | ~ r2_hidden(D_242,k1_relat_1(A_241))
      | ~ v1_funct_1(A_241)
      | ~ v1_relat_1(A_241) ) ),
    inference(resolution,[status(thm)],[c_307,c_32])).

tff(c_794,plain,(
    ! [D_242] :
      ( r2_hidden(k1_funct_1('#skF_10',D_242),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_242,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_306,c_792])).

tff(c_798,plain,(
    ! [D_244] :
      ( r2_hidden(k1_funct_1('#skF_10',D_244),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_244,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_84,c_398,c_794])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_225,plain,(
    ! [E_133,C_134,B_135,A_136] :
      ( E_133 = C_134
      | E_133 = B_135
      | E_133 = A_136
      | ~ r2_hidden(E_133,k1_enumset1(A_136,B_135,C_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_248,plain,(
    ! [E_141,B_142,A_143] :
      ( E_141 = B_142
      | E_141 = A_143
      | E_141 = A_143
      | ~ r2_hidden(E_141,k2_tarski(A_143,B_142)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_225])).

tff(c_257,plain,(
    ! [E_141,A_9] :
      ( E_141 = A_9
      | E_141 = A_9
      | E_141 = A_9
      | ~ r2_hidden(E_141,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_248])).

tff(c_818,plain,(
    ! [D_245] :
      ( k1_funct_1('#skF_10',D_245) = '#skF_8'
      | ~ r2_hidden(D_245,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_798,c_257])).

tff(c_866,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_78,c_818])).

tff(c_882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_866])).

tff(c_883,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_118,plain,(
    ! [A_96,B_97] : k1_enumset1(A_96,A_96,B_97) = k2_tarski(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [E_8,B_3,C_4] : r2_hidden(E_8,k1_enumset1(E_8,B_3,C_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_142,plain,(
    ! [A_98,B_99] : r2_hidden(A_98,k2_tarski(A_98,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_10])).

tff(c_150,plain,(
    ! [A_100] : r2_hidden(A_100,k1_tarski(A_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_142])).

tff(c_56,plain,(
    ! [B_62,A_61] :
      ( ~ r1_tarski(B_62,A_61)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_154,plain,(
    ! [A_100] : ~ r1_tarski(k1_tarski(A_100),A_100) ),
    inference(resolution,[status(thm)],[c_150,c_56])).

tff(c_900,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_154])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:01:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.63  
% 3.85/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.63  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 3.85/1.63  
% 3.85/1.63  %Foreground sorts:
% 3.85/1.63  
% 3.85/1.63  
% 3.85/1.63  %Background operators:
% 3.85/1.63  
% 3.85/1.63  
% 3.85/1.63  %Foreground operators:
% 3.85/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.85/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.63  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.85/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.85/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.85/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.85/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.63  tff('#skF_10', type, '#skF_10': $i).
% 3.85/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.85/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.85/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.85/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.85/1.63  tff('#skF_9', type, '#skF_9': $i).
% 3.85/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.85/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.85/1.63  tff('#skF_8', type, '#skF_8': $i).
% 3.85/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.85/1.63  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.85/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.85/1.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.85/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.63  
% 3.85/1.65  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.85/1.65  tff(f_123, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.85/1.65  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.85/1.65  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.85/1.65  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.85/1.65  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.85/1.65  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.85/1.65  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.85/1.65  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.85/1.65  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.85/1.65  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.85/1.65  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.85/1.65  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.85/1.65  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.85/1.65  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.65  tff(c_76, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.85/1.65  tff(c_78, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.85/1.65  tff(c_36, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.85/1.65  tff(c_80, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.85/1.65  tff(c_156, plain, (![B_102, A_103]: (v1_relat_1(B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_103)) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.85/1.65  tff(c_159, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_80, c_156])).
% 3.85/1.65  tff(c_162, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_159])).
% 3.85/1.65  tff(c_84, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.85/1.65  tff(c_82, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.85/1.65  tff(c_277, plain, (![A_149, B_150, C_151]: (k1_relset_1(A_149, B_150, C_151)=k1_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.85/1.65  tff(c_281, plain, (k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_80, c_277])).
% 3.85/1.65  tff(c_386, plain, (![B_180, A_181, C_182]: (k1_xboole_0=B_180 | k1_relset_1(A_181, B_180, C_182)=A_181 | ~v1_funct_2(C_182, A_181, B_180) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_181, B_180))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.85/1.65  tff(c_393, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_80, c_386])).
% 3.85/1.65  tff(c_397, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_281, c_393])).
% 3.85/1.65  tff(c_398, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_397])).
% 3.85/1.65  tff(c_268, plain, (![A_146, B_147, C_148]: (k2_relset_1(A_146, B_147, C_148)=k2_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.85/1.65  tff(c_272, plain, (k2_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_80, c_268])).
% 3.85/1.65  tff(c_287, plain, (![A_153, B_154, C_155]: (m1_subset_1(k2_relset_1(A_153, B_154, C_155), k1_zfmisc_1(B_154)) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.85/1.65  tff(c_301, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_272, c_287])).
% 3.85/1.65  tff(c_306, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_301])).
% 3.85/1.65  tff(c_307, plain, (![A_156, D_157]: (r2_hidden(k1_funct_1(A_156, D_157), k2_relat_1(A_156)) | ~r2_hidden(D_157, k1_relat_1(A_156)) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/1.65  tff(c_32, plain, (![C_15, A_12, B_13]: (r2_hidden(C_15, A_12) | ~r2_hidden(C_15, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.65  tff(c_792, plain, (![A_241, D_242, A_243]: (r2_hidden(k1_funct_1(A_241, D_242), A_243) | ~m1_subset_1(k2_relat_1(A_241), k1_zfmisc_1(A_243)) | ~r2_hidden(D_242, k1_relat_1(A_241)) | ~v1_funct_1(A_241) | ~v1_relat_1(A_241))), inference(resolution, [status(thm)], [c_307, c_32])).
% 3.85/1.65  tff(c_794, plain, (![D_242]: (r2_hidden(k1_funct_1('#skF_10', D_242), k1_tarski('#skF_8')) | ~r2_hidden(D_242, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_306, c_792])).
% 3.85/1.65  tff(c_798, plain, (![D_244]: (r2_hidden(k1_funct_1('#skF_10', D_244), k1_tarski('#skF_8')) | ~r2_hidden(D_244, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_84, c_398, c_794])).
% 3.85/1.65  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.85/1.65  tff(c_30, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.85/1.65  tff(c_225, plain, (![E_133, C_134, B_135, A_136]: (E_133=C_134 | E_133=B_135 | E_133=A_136 | ~r2_hidden(E_133, k1_enumset1(A_136, B_135, C_134)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.85/1.65  tff(c_248, plain, (![E_141, B_142, A_143]: (E_141=B_142 | E_141=A_143 | E_141=A_143 | ~r2_hidden(E_141, k2_tarski(A_143, B_142)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_225])).
% 3.85/1.65  tff(c_257, plain, (![E_141, A_9]: (E_141=A_9 | E_141=A_9 | E_141=A_9 | ~r2_hidden(E_141, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_248])).
% 3.85/1.65  tff(c_818, plain, (![D_245]: (k1_funct_1('#skF_10', D_245)='#skF_8' | ~r2_hidden(D_245, '#skF_7'))), inference(resolution, [status(thm)], [c_798, c_257])).
% 3.85/1.65  tff(c_866, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_78, c_818])).
% 3.85/1.65  tff(c_882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_866])).
% 3.85/1.65  tff(c_883, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_397])).
% 3.85/1.65  tff(c_118, plain, (![A_96, B_97]: (k1_enumset1(A_96, A_96, B_97)=k2_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.85/1.65  tff(c_10, plain, (![E_8, B_3, C_4]: (r2_hidden(E_8, k1_enumset1(E_8, B_3, C_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.85/1.65  tff(c_142, plain, (![A_98, B_99]: (r2_hidden(A_98, k2_tarski(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_10])).
% 3.85/1.65  tff(c_150, plain, (![A_100]: (r2_hidden(A_100, k1_tarski(A_100)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_142])).
% 3.85/1.65  tff(c_56, plain, (![B_62, A_61]: (~r1_tarski(B_62, A_61) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.85/1.65  tff(c_154, plain, (![A_100]: (~r1_tarski(k1_tarski(A_100), A_100))), inference(resolution, [status(thm)], [c_150, c_56])).
% 3.85/1.65  tff(c_900, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_883, c_154])).
% 3.85/1.65  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_900])).
% 3.85/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.65  
% 3.85/1.65  Inference rules
% 3.85/1.65  ----------------------
% 3.85/1.65  #Ref     : 0
% 3.85/1.65  #Sup     : 179
% 3.85/1.65  #Fact    : 0
% 3.85/1.65  #Define  : 0
% 3.85/1.65  #Split   : 7
% 3.85/1.65  #Chain   : 0
% 3.85/1.65  #Close   : 0
% 3.85/1.65  
% 3.85/1.65  Ordering : KBO
% 3.85/1.65  
% 3.85/1.65  Simplification rules
% 3.85/1.65  ----------------------
% 3.85/1.65  #Subsume      : 20
% 3.85/1.65  #Demod        : 66
% 3.85/1.65  #Tautology    : 30
% 3.85/1.65  #SimpNegUnit  : 2
% 3.85/1.65  #BackRed      : 19
% 3.85/1.65  
% 3.85/1.65  #Partial instantiations: 0
% 3.85/1.65  #Strategies tried      : 1
% 3.85/1.65  
% 3.85/1.65  Timing (in seconds)
% 3.85/1.65  ----------------------
% 3.85/1.65  Preprocessing        : 0.38
% 3.85/1.65  Parsing              : 0.18
% 3.85/1.65  CNF conversion       : 0.03
% 3.85/1.65  Main loop            : 0.49
% 3.85/1.65  Inferencing          : 0.17
% 3.85/1.65  Reduction            : 0.15
% 3.85/1.65  Demodulation         : 0.10
% 3.85/1.65  BG Simplification    : 0.03
% 3.85/1.65  Subsumption          : 0.10
% 3.85/1.65  Abstraction          : 0.03
% 3.85/1.65  MUC search           : 0.00
% 3.85/1.65  Cooper               : 0.00
% 3.85/1.65  Total                : 0.90
% 3.85/1.65  Index Insertion      : 0.00
% 3.85/1.65  Index Deletion       : 0.00
% 3.85/1.65  Index Matching       : 0.00
% 3.85/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
