%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:04 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 132 expanded)
%              Number of leaves         :   48 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  135 ( 260 expanded)
%              Number of equality atoms :   39 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_42,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_86,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_133,plain,(
    ! [B_101,A_102] :
      ( v1_relat_1(B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102))
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_136,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_86,c_133])).

tff(c_139,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_136])).

tff(c_90,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    ! [A_28,C_64] :
      ( k1_funct_1(A_28,'#skF_6'(A_28,k2_relat_1(A_28),C_64)) = C_64
      | ~ r2_hidden(C_64,k2_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_146,plain,(
    ! [C_109,B_110,A_111] :
      ( v5_relat_1(C_109,B_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_150,plain,(
    v5_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_146])).

tff(c_272,plain,(
    ! [A_152,B_153,C_154] :
      ( k2_relset_1(A_152,B_153,C_154) = k2_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_276,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_86,c_272])).

tff(c_84,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_279,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_84])).

tff(c_200,plain,(
    ! [B_128,A_129] :
      ( r1_tarski(k2_relat_1(B_128),A_129)
      | ~ v5_relat_1(B_128,A_129)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_219,plain,(
    ! [B_135,A_136] :
      ( k2_xboole_0(k2_relat_1(B_135),A_136) = A_136
      | ~ v5_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_200,c_20])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_110,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k1_tarski(A_94),B_95)
      | ~ r2_hidden(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_152,plain,(
    ! [A_115,B_116] :
      ( k2_xboole_0(k1_tarski(A_115),B_116) = B_116
      | ~ r2_hidden(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_110,c_20])).

tff(c_32,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),B_18) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_176,plain,(
    ! [B_117,A_118] :
      ( k1_xboole_0 != B_117
      | ~ r2_hidden(A_118,B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_32])).

tff(c_186,plain,(
    ! [A_1,B_2,D_6] :
      ( k2_xboole_0(A_1,B_2) != k1_xboole_0
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(resolution,[status(thm)],[c_6,c_176])).

tff(c_226,plain,(
    ! [A_136,D_6,B_135] :
      ( k1_xboole_0 != A_136
      | ~ r2_hidden(D_6,k2_relat_1(B_135))
      | ~ v5_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_186])).

tff(c_285,plain,(
    ! [A_136] :
      ( k1_xboole_0 != A_136
      | ~ v5_relat_1('#skF_10',A_136)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_279,c_226])).

tff(c_299,plain,(
    ! [A_155] :
      ( k1_xboole_0 != A_155
      | ~ v5_relat_1('#skF_10',A_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_285])).

tff(c_303,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(resolution,[status(thm)],[c_150,c_299])).

tff(c_88,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_263,plain,(
    ! [A_149,B_150,C_151] :
      ( k1_relset_1(A_149,B_150,C_151) = k1_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_267,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_86,c_263])).

tff(c_423,plain,(
    ! [B_193,A_194,C_195] :
      ( k1_xboole_0 = B_193
      | k1_relset_1(A_194,B_193,C_195) = A_194
      | ~ v1_funct_2(C_195,A_194,B_193)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_426,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_423])).

tff(c_429,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_267,c_426])).

tff(c_430,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_429])).

tff(c_48,plain,(
    ! [A_28,C_64] :
      ( r2_hidden('#skF_6'(A_28,k2_relat_1(A_28),C_64),k1_relat_1(A_28))
      | ~ r2_hidden(C_64,k2_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_435,plain,(
    ! [C_64] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_64),'#skF_8')
      | ~ r2_hidden(C_64,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_48])).

tff(c_450,plain,(
    ! [C_196] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_196),'#skF_8')
      | ~ r2_hidden(C_196,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_435])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_460,plain,(
    ! [C_197] :
      ( m1_subset_1('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_197),'#skF_8')
      | ~ r2_hidden(C_197,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_450,c_34])).

tff(c_82,plain,(
    ! [E_81] :
      ( k1_funct_1('#skF_10',E_81) != '#skF_7'
      | ~ m1_subset_1(E_81,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_476,plain,(
    ! [C_200] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_200)) != '#skF_7'
      | ~ r2_hidden(C_200,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_460,c_82])).

tff(c_480,plain,(
    ! [C_64] :
      ( C_64 != '#skF_7'
      | ~ r2_hidden(C_64,k2_relat_1('#skF_10'))
      | ~ r2_hidden(C_64,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_476])).

tff(c_483,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_480])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_483,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:38:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.49  
% 3.05/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 3.05/1.49  
% 3.05/1.49  %Foreground sorts:
% 3.05/1.49  
% 3.05/1.49  
% 3.05/1.49  %Background operators:
% 3.05/1.49  
% 3.05/1.49  
% 3.05/1.49  %Foreground operators:
% 3.05/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.05/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.05/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.49  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.05/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.05/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.05/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.05/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.05/1.49  tff('#skF_10', type, '#skF_10': $i).
% 3.05/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.05/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.05/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.05/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.05/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.05/1.49  tff('#skF_9', type, '#skF_9': $i).
% 3.05/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.05/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.05/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.05/1.49  tff('#skF_8', type, '#skF_8': $i).
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.05/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.05/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.05/1.49  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.05/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.05/1.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.05/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.49  
% 3.12/1.51  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.12/1.51  tff(f_133, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 3.12/1.51  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.12/1.51  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.12/1.51  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.12/1.51  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.12/1.51  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.12/1.51  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.12/1.51  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.12/1.51  tff(f_48, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.12/1.51  tff(f_51, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.12/1.51  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.12/1.51  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.12/1.51  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.12/1.51  tff(c_42, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.12/1.51  tff(c_86, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.12/1.51  tff(c_133, plain, (![B_101, A_102]: (v1_relat_1(B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.12/1.51  tff(c_136, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_86, c_133])).
% 3.12/1.51  tff(c_139, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_136])).
% 3.12/1.51  tff(c_90, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.12/1.51  tff(c_46, plain, (![A_28, C_64]: (k1_funct_1(A_28, '#skF_6'(A_28, k2_relat_1(A_28), C_64))=C_64 | ~r2_hidden(C_64, k2_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.12/1.51  tff(c_146, plain, (![C_109, B_110, A_111]: (v5_relat_1(C_109, B_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.12/1.51  tff(c_150, plain, (v5_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_86, c_146])).
% 3.12/1.51  tff(c_272, plain, (![A_152, B_153, C_154]: (k2_relset_1(A_152, B_153, C_154)=k2_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.12/1.51  tff(c_276, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_86, c_272])).
% 3.12/1.51  tff(c_84, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.12/1.51  tff(c_279, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_84])).
% 3.12/1.51  tff(c_200, plain, (![B_128, A_129]: (r1_tarski(k2_relat_1(B_128), A_129) | ~v5_relat_1(B_128, A_129) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.12/1.51  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.12/1.51  tff(c_219, plain, (![B_135, A_136]: (k2_xboole_0(k2_relat_1(B_135), A_136)=A_136 | ~v5_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_200, c_20])).
% 3.12/1.51  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.12/1.51  tff(c_110, plain, (![A_94, B_95]: (r1_tarski(k1_tarski(A_94), B_95) | ~r2_hidden(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.12/1.51  tff(c_152, plain, (![A_115, B_116]: (k2_xboole_0(k1_tarski(A_115), B_116)=B_116 | ~r2_hidden(A_115, B_116))), inference(resolution, [status(thm)], [c_110, c_20])).
% 3.12/1.51  tff(c_32, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.12/1.51  tff(c_176, plain, (![B_117, A_118]: (k1_xboole_0!=B_117 | ~r2_hidden(A_118, B_117))), inference(superposition, [status(thm), theory('equality')], [c_152, c_32])).
% 3.12/1.51  tff(c_186, plain, (![A_1, B_2, D_6]: (k2_xboole_0(A_1, B_2)!=k1_xboole_0 | ~r2_hidden(D_6, A_1))), inference(resolution, [status(thm)], [c_6, c_176])).
% 3.12/1.51  tff(c_226, plain, (![A_136, D_6, B_135]: (k1_xboole_0!=A_136 | ~r2_hidden(D_6, k2_relat_1(B_135)) | ~v5_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(superposition, [status(thm), theory('equality')], [c_219, c_186])).
% 3.12/1.51  tff(c_285, plain, (![A_136]: (k1_xboole_0!=A_136 | ~v5_relat_1('#skF_10', A_136) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_279, c_226])).
% 3.12/1.51  tff(c_299, plain, (![A_155]: (k1_xboole_0!=A_155 | ~v5_relat_1('#skF_10', A_155))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_285])).
% 3.12/1.51  tff(c_303, plain, (k1_xboole_0!='#skF_9'), inference(resolution, [status(thm)], [c_150, c_299])).
% 3.12/1.51  tff(c_88, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.12/1.51  tff(c_263, plain, (![A_149, B_150, C_151]: (k1_relset_1(A_149, B_150, C_151)=k1_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.12/1.51  tff(c_267, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_86, c_263])).
% 3.12/1.51  tff(c_423, plain, (![B_193, A_194, C_195]: (k1_xboole_0=B_193 | k1_relset_1(A_194, B_193, C_195)=A_194 | ~v1_funct_2(C_195, A_194, B_193) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.12/1.51  tff(c_426, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_86, c_423])).
% 3.12/1.51  tff(c_429, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_267, c_426])).
% 3.12/1.51  tff(c_430, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_303, c_429])).
% 3.12/1.51  tff(c_48, plain, (![A_28, C_64]: (r2_hidden('#skF_6'(A_28, k2_relat_1(A_28), C_64), k1_relat_1(A_28)) | ~r2_hidden(C_64, k2_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.12/1.51  tff(c_435, plain, (![C_64]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_64), '#skF_8') | ~r2_hidden(C_64, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_430, c_48])).
% 3.12/1.51  tff(c_450, plain, (![C_196]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_196), '#skF_8') | ~r2_hidden(C_196, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_435])).
% 3.12/1.51  tff(c_34, plain, (![A_19, B_20]: (m1_subset_1(A_19, B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.12/1.51  tff(c_460, plain, (![C_197]: (m1_subset_1('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_197), '#skF_8') | ~r2_hidden(C_197, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_450, c_34])).
% 3.12/1.51  tff(c_82, plain, (![E_81]: (k1_funct_1('#skF_10', E_81)!='#skF_7' | ~m1_subset_1(E_81, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.12/1.51  tff(c_476, plain, (![C_200]: (k1_funct_1('#skF_10', '#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_200))!='#skF_7' | ~r2_hidden(C_200, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_460, c_82])).
% 3.12/1.51  tff(c_480, plain, (![C_64]: (C_64!='#skF_7' | ~r2_hidden(C_64, k2_relat_1('#skF_10')) | ~r2_hidden(C_64, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_476])).
% 3.12/1.51  tff(c_483, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_480])).
% 3.12/1.51  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_483, c_279])).
% 3.12/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.51  
% 3.12/1.51  Inference rules
% 3.12/1.51  ----------------------
% 3.12/1.51  #Ref     : 0
% 3.12/1.51  #Sup     : 88
% 3.12/1.51  #Fact    : 0
% 3.12/1.51  #Define  : 0
% 3.12/1.51  #Split   : 1
% 3.12/1.51  #Chain   : 0
% 3.12/1.51  #Close   : 0
% 3.12/1.51  
% 3.12/1.51  Ordering : KBO
% 3.12/1.51  
% 3.12/1.51  Simplification rules
% 3.12/1.51  ----------------------
% 3.12/1.51  #Subsume      : 13
% 3.12/1.51  #Demod        : 23
% 3.12/1.51  #Tautology    : 31
% 3.12/1.51  #SimpNegUnit  : 2
% 3.12/1.51  #BackRed      : 5
% 3.12/1.51  
% 3.12/1.51  #Partial instantiations: 0
% 3.12/1.51  #Strategies tried      : 1
% 3.12/1.51  
% 3.12/1.51  Timing (in seconds)
% 3.12/1.51  ----------------------
% 3.12/1.51  Preprocessing        : 0.36
% 3.12/1.51  Parsing              : 0.18
% 3.12/1.51  CNF conversion       : 0.03
% 3.12/1.51  Main loop            : 0.38
% 3.12/1.51  Inferencing          : 0.14
% 3.12/1.51  Reduction            : 0.10
% 3.12/1.51  Demodulation         : 0.07
% 3.12/1.51  BG Simplification    : 0.02
% 3.12/1.51  Subsumption          : 0.08
% 3.12/1.51  Abstraction          : 0.02
% 3.12/1.51  MUC search           : 0.00
% 3.12/1.51  Cooper               : 0.00
% 3.12/1.51  Total                : 0.77
% 3.12/1.51  Index Insertion      : 0.00
% 3.12/1.52  Index Deletion       : 0.00
% 3.12/1.52  Index Matching       : 0.00
% 3.12/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
