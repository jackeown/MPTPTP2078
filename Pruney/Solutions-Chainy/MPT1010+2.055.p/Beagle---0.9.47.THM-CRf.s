%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:12 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 113 expanded)
%              Number of leaves         :   43 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 210 expanded)
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

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_68,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_76,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_78,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_157,plain,(
    ! [C_101,A_102,B_103] :
      ( v1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_161,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_157])).

tff(c_82,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_80,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_263,plain,(
    ! [A_143,B_144,C_145] :
      ( k1_relset_1(A_143,B_144,C_145) = k1_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_267,plain,(
    k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_263])).

tff(c_360,plain,(
    ! [B_173,A_174,C_175] :
      ( k1_xboole_0 = B_173
      | k1_relset_1(A_174,B_173,C_175) = A_174
      | ~ v1_funct_2(C_175,A_174,B_173)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_367,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_78,c_360])).

tff(c_371,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_267,c_367])).

tff(c_372,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_371])).

tff(c_272,plain,(
    ! [A_146,B_147,C_148] :
      ( k2_relset_1(A_146,B_147,C_148) = k2_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_276,plain,(
    k2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_272])).

tff(c_282,plain,(
    ! [A_150,B_151,C_152] :
      ( m1_subset_1(k2_relset_1(A_150,B_151,C_152),k1_zfmisc_1(B_151))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_297,plain,
    ( m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_282])).

tff(c_302,plain,(
    m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_297])).

tff(c_303,plain,(
    ! [A_153,D_154] :
      ( r2_hidden(k1_funct_1(A_153,D_154),k2_relat_1(A_153))
      | ~ r2_hidden(D_154,k1_relat_1(A_153))
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ! [C_15,A_12,B_13] :
      ( r2_hidden(C_15,A_12)
      | ~ r2_hidden(C_15,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_858,plain,(
    ! [A_255,D_256,A_257] :
      ( r2_hidden(k1_funct_1(A_255,D_256),A_257)
      | ~ m1_subset_1(k2_relat_1(A_255),k1_zfmisc_1(A_257))
      | ~ r2_hidden(D_256,k1_relat_1(A_255))
      | ~ v1_funct_1(A_255)
      | ~ v1_relat_1(A_255) ) ),
    inference(resolution,[status(thm)],[c_303,c_32])).

tff(c_860,plain,(
    ! [D_256] :
      ( r2_hidden(k1_funct_1('#skF_10',D_256),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_256,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_302,c_858])).

tff(c_864,plain,(
    ! [D_258] :
      ( r2_hidden(k1_funct_1('#skF_10',D_258),k1_tarski('#skF_8'))
      | ~ r2_hidden(D_258,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_82,c_372,c_860])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_220,plain,(
    ! [E_130,C_131,B_132,A_133] :
      ( E_130 = C_131
      | E_130 = B_132
      | E_130 = A_133
      | ~ r2_hidden(E_130,k1_enumset1(A_133,B_132,C_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_243,plain,(
    ! [E_138,B_139,A_140] :
      ( E_138 = B_139
      | E_138 = A_140
      | E_138 = A_140
      | ~ r2_hidden(E_138,k2_tarski(A_140,B_139)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_220])).

tff(c_252,plain,(
    ! [E_138,A_9] :
      ( E_138 = A_9
      | E_138 = A_9
      | E_138 = A_9
      | ~ r2_hidden(E_138,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_243])).

tff(c_884,plain,(
    ! [D_259] :
      ( k1_funct_1('#skF_10',D_259) = '#skF_8'
      | ~ r2_hidden(D_259,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_864,c_252])).

tff(c_940,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_76,c_884])).

tff(c_958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_940])).

tff(c_959,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_116,plain,(
    ! [A_95,B_96] : k1_enumset1(A_95,A_95,B_96) = k2_tarski(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [E_8,A_2,B_3] : r2_hidden(E_8,k1_enumset1(A_2,B_3,E_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_143,plain,(
    ! [B_97,A_98] : r2_hidden(B_97,k2_tarski(A_98,B_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_6])).

tff(c_151,plain,(
    ! [A_99] : r2_hidden(A_99,k1_tarski(A_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_143])).

tff(c_52,plain,(
    ! [B_57,A_56] :
      ( ~ r1_tarski(B_57,A_56)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_155,plain,(
    ! [A_99] : ~ r1_tarski(k1_tarski(A_99),A_99) ),
    inference(resolution,[status(thm)],[c_151,c_52])).

tff(c_976,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_155])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_976])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.61  
% 3.49/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.61  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 3.49/1.61  
% 3.49/1.61  %Foreground sorts:
% 3.49/1.61  
% 3.49/1.61  
% 3.49/1.61  %Background operators:
% 3.49/1.61  
% 3.49/1.61  
% 3.49/1.61  %Foreground operators:
% 3.49/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.49/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.61  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.49/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.49/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.49/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.61  tff('#skF_10', type, '#skF_10': $i).
% 3.49/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.49/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.49/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.49/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.49/1.61  tff('#skF_9', type, '#skF_9': $i).
% 3.49/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.49/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.49/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.49/1.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.49/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.61  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.49/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.61  
% 3.83/1.63  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.83/1.63  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.83/1.63  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.83/1.63  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.83/1.63  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.83/1.63  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.83/1.63  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.83/1.63  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.83/1.63  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.83/1.63  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.83/1.63  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.83/1.63  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.83/1.63  tff(f_73, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.83/1.63  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.83/1.63  tff(c_74, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.83/1.63  tff(c_76, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.83/1.63  tff(c_78, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.83/1.63  tff(c_157, plain, (![C_101, A_102, B_103]: (v1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.83/1.63  tff(c_161, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_157])).
% 3.83/1.63  tff(c_82, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.83/1.63  tff(c_80, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.83/1.63  tff(c_263, plain, (![A_143, B_144, C_145]: (k1_relset_1(A_143, B_144, C_145)=k1_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.83/1.63  tff(c_267, plain, (k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_263])).
% 3.83/1.63  tff(c_360, plain, (![B_173, A_174, C_175]: (k1_xboole_0=B_173 | k1_relset_1(A_174, B_173, C_175)=A_174 | ~v1_funct_2(C_175, A_174, B_173) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.83/1.63  tff(c_367, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_78, c_360])).
% 3.83/1.63  tff(c_371, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_267, c_367])).
% 3.83/1.63  tff(c_372, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_371])).
% 3.83/1.63  tff(c_272, plain, (![A_146, B_147, C_148]: (k2_relset_1(A_146, B_147, C_148)=k2_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.83/1.63  tff(c_276, plain, (k2_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_272])).
% 3.83/1.63  tff(c_282, plain, (![A_150, B_151, C_152]: (m1_subset_1(k2_relset_1(A_150, B_151, C_152), k1_zfmisc_1(B_151)) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.83/1.63  tff(c_297, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_276, c_282])).
% 3.83/1.63  tff(c_302, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_297])).
% 3.83/1.63  tff(c_303, plain, (![A_153, D_154]: (r2_hidden(k1_funct_1(A_153, D_154), k2_relat_1(A_153)) | ~r2_hidden(D_154, k1_relat_1(A_153)) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.83/1.63  tff(c_32, plain, (![C_15, A_12, B_13]: (r2_hidden(C_15, A_12) | ~r2_hidden(C_15, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.83/1.63  tff(c_858, plain, (![A_255, D_256, A_257]: (r2_hidden(k1_funct_1(A_255, D_256), A_257) | ~m1_subset_1(k2_relat_1(A_255), k1_zfmisc_1(A_257)) | ~r2_hidden(D_256, k1_relat_1(A_255)) | ~v1_funct_1(A_255) | ~v1_relat_1(A_255))), inference(resolution, [status(thm)], [c_303, c_32])).
% 3.83/1.63  tff(c_860, plain, (![D_256]: (r2_hidden(k1_funct_1('#skF_10', D_256), k1_tarski('#skF_8')) | ~r2_hidden(D_256, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_302, c_858])).
% 3.83/1.63  tff(c_864, plain, (![D_258]: (r2_hidden(k1_funct_1('#skF_10', D_258), k1_tarski('#skF_8')) | ~r2_hidden(D_258, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_82, c_372, c_860])).
% 3.83/1.63  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.83/1.63  tff(c_30, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.83/1.63  tff(c_220, plain, (![E_130, C_131, B_132, A_133]: (E_130=C_131 | E_130=B_132 | E_130=A_133 | ~r2_hidden(E_130, k1_enumset1(A_133, B_132, C_131)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.83/1.63  tff(c_243, plain, (![E_138, B_139, A_140]: (E_138=B_139 | E_138=A_140 | E_138=A_140 | ~r2_hidden(E_138, k2_tarski(A_140, B_139)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_220])).
% 3.83/1.63  tff(c_252, plain, (![E_138, A_9]: (E_138=A_9 | E_138=A_9 | E_138=A_9 | ~r2_hidden(E_138, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_243])).
% 3.83/1.63  tff(c_884, plain, (![D_259]: (k1_funct_1('#skF_10', D_259)='#skF_8' | ~r2_hidden(D_259, '#skF_7'))), inference(resolution, [status(thm)], [c_864, c_252])).
% 3.83/1.63  tff(c_940, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_76, c_884])).
% 3.83/1.63  tff(c_958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_940])).
% 3.83/1.63  tff(c_959, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_371])).
% 3.83/1.63  tff(c_116, plain, (![A_95, B_96]: (k1_enumset1(A_95, A_95, B_96)=k2_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.83/1.63  tff(c_6, plain, (![E_8, A_2, B_3]: (r2_hidden(E_8, k1_enumset1(A_2, B_3, E_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.83/1.63  tff(c_143, plain, (![B_97, A_98]: (r2_hidden(B_97, k2_tarski(A_98, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_6])).
% 3.83/1.63  tff(c_151, plain, (![A_99]: (r2_hidden(A_99, k1_tarski(A_99)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_143])).
% 3.83/1.63  tff(c_52, plain, (![B_57, A_56]: (~r1_tarski(B_57, A_56) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.83/1.63  tff(c_155, plain, (![A_99]: (~r1_tarski(k1_tarski(A_99), A_99))), inference(resolution, [status(thm)], [c_151, c_52])).
% 3.83/1.63  tff(c_976, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_959, c_155])).
% 3.83/1.63  tff(c_984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_976])).
% 3.83/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.63  
% 3.83/1.63  Inference rules
% 3.83/1.63  ----------------------
% 3.83/1.63  #Ref     : 0
% 3.83/1.63  #Sup     : 196
% 3.83/1.63  #Fact    : 0
% 3.83/1.63  #Define  : 0
% 3.83/1.63  #Split   : 6
% 3.83/1.63  #Chain   : 0
% 3.83/1.63  #Close   : 0
% 3.83/1.63  
% 3.83/1.63  Ordering : KBO
% 3.83/1.63  
% 3.83/1.63  Simplification rules
% 3.83/1.63  ----------------------
% 3.83/1.63  #Subsume      : 22
% 3.83/1.63  #Demod        : 65
% 3.83/1.63  #Tautology    : 31
% 3.83/1.63  #SimpNegUnit  : 3
% 3.83/1.63  #BackRed      : 18
% 3.83/1.63  
% 3.83/1.63  #Partial instantiations: 0
% 3.83/1.63  #Strategies tried      : 1
% 3.83/1.63  
% 3.83/1.63  Timing (in seconds)
% 3.83/1.63  ----------------------
% 3.83/1.63  Preprocessing        : 0.36
% 3.83/1.63  Parsing              : 0.18
% 3.83/1.63  CNF conversion       : 0.03
% 3.83/1.63  Main loop            : 0.50
% 3.83/1.63  Inferencing          : 0.18
% 3.83/1.63  Reduction            : 0.15
% 3.83/1.63  Demodulation         : 0.10
% 3.83/1.63  BG Simplification    : 0.03
% 3.83/1.63  Subsumption          : 0.10
% 3.83/1.63  Abstraction          : 0.03
% 3.83/1.63  MUC search           : 0.00
% 3.83/1.63  Cooper               : 0.00
% 3.83/1.63  Total                : 0.89
% 3.83/1.63  Index Insertion      : 0.00
% 3.83/1.63  Index Deletion       : 0.00
% 3.83/1.63  Index Matching       : 0.00
% 3.83/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
