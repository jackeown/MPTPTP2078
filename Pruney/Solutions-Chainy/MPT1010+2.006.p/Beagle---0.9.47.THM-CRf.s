%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:06 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 130 expanded)
%              Number of leaves         :   49 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 247 expanded)
%              Number of equality atoms :   45 (  83 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_90,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,(
    k1_funct_1('#skF_11','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_92,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_251,plain,(
    ! [C_130,B_131,A_132] :
      ( v5_relat_1(C_130,B_131)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_260,plain,(
    v5_relat_1('#skF_11',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_92,c_251])).

tff(c_90,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_189,plain,(
    ! [C_109,A_110,B_111] :
      ( v1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_198,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_92,c_189])).

tff(c_96,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_94,plain,(
    v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_388,plain,(
    ! [A_170,B_171,C_172] :
      ( k1_relset_1(A_170,B_171,C_172) = k1_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_402,plain,(
    k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_92,c_388])).

tff(c_892,plain,(
    ! [B_254,A_255,C_256] :
      ( k1_xboole_0 = B_254
      | k1_relset_1(A_255,B_254,C_256) = A_255
      | ~ v1_funct_2(C_256,A_255,B_254)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_903,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_92,c_892])).

tff(c_908,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_402,c_903])).

tff(c_909,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_908])).

tff(c_48,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_597,plain,(
    ! [A_196,D_197] :
      ( r2_hidden(k1_funct_1(A_196,D_197),k2_relat_1(A_196))
      | ~ r2_hidden(D_197,k1_relat_1(A_196))
      | ~ v1_funct_1(A_196)
      | ~ v1_relat_1(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_261,plain,(
    ! [A_133,C_134,B_135] :
      ( m1_subset_1(A_133,C_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(C_134))
      | ~ r2_hidden(A_133,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_266,plain,(
    ! [A_133,B_21,A_20] :
      ( m1_subset_1(A_133,B_21)
      | ~ r2_hidden(A_133,A_20)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_42,c_261])).

tff(c_2267,plain,(
    ! [A_422,D_423,B_424] :
      ( m1_subset_1(k1_funct_1(A_422,D_423),B_424)
      | ~ r1_tarski(k2_relat_1(A_422),B_424)
      | ~ r2_hidden(D_423,k1_relat_1(A_422))
      | ~ v1_funct_1(A_422)
      | ~ v1_relat_1(A_422) ) ),
    inference(resolution,[status(thm)],[c_597,c_266])).

tff(c_2271,plain,(
    ! [B_425,D_426,A_427] :
      ( m1_subset_1(k1_funct_1(B_425,D_426),A_427)
      | ~ r2_hidden(D_426,k1_relat_1(B_425))
      | ~ v1_funct_1(B_425)
      | ~ v5_relat_1(B_425,A_427)
      | ~ v1_relat_1(B_425) ) ),
    inference(resolution,[status(thm)],[c_48,c_2267])).

tff(c_2292,plain,(
    ! [D_426,A_427] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_426),A_427)
      | ~ r2_hidden(D_426,'#skF_8')
      | ~ v1_funct_1('#skF_11')
      | ~ v5_relat_1('#skF_11',A_427)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_909,c_2271])).

tff(c_2317,plain,(
    ! [D_428,A_429] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_428),A_429)
      | ~ r2_hidden(D_428,'#skF_8')
      | ~ v5_relat_1('#skF_11',A_429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_96,c_2292])).

tff(c_32,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_137,plain,(
    ! [A_97,B_98] : k1_enumset1(A_97,A_97,B_98) = k2_tarski(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_116,plain,(
    ! [E_83,A_84,B_85] : r2_hidden(E_83,k1_enumset1(A_84,B_85,E_83)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_84,B_85,E_83] : ~ v1_xboole_0(k1_enumset1(A_84,B_85,E_83)) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_148,plain,(
    ! [A_97,B_98] : ~ v1_xboole_0(k2_tarski(A_97,B_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_120])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_322,plain,(
    ! [E_156,C_157,B_158,A_159] :
      ( E_156 = C_157
      | E_156 = B_158
      | E_156 = A_159
      | ~ r2_hidden(E_156,k1_enumset1(A_159,B_158,C_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_424,plain,(
    ! [E_178,B_179,A_180] :
      ( E_178 = B_179
      | E_178 = A_180
      | E_178 = A_180
      | ~ r2_hidden(E_178,k2_tarski(A_180,B_179)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_322])).

tff(c_428,plain,(
    ! [B_179,A_18,A_180] :
      ( B_179 = A_18
      | A_180 = A_18
      | v1_xboole_0(k2_tarski(A_180,B_179))
      | ~ m1_subset_1(A_18,k2_tarski(A_180,B_179)) ) ),
    inference(resolution,[status(thm)],[c_38,c_424])).

tff(c_452,plain,(
    ! [B_181,A_182,A_183] :
      ( B_181 = A_182
      | A_183 = A_182
      | ~ m1_subset_1(A_182,k2_tarski(A_183,B_181)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_428])).

tff(c_459,plain,(
    ! [A_182,A_12] :
      ( A_182 = A_12
      | A_182 = A_12
      | ~ m1_subset_1(A_182,k1_tarski(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_452])).

tff(c_2405,plain,(
    ! [D_430,A_431] :
      ( k1_funct_1('#skF_11',D_430) = A_431
      | ~ r2_hidden(D_430,'#skF_8')
      | ~ v5_relat_1('#skF_11',k1_tarski(A_431)) ) ),
    inference(resolution,[status(thm)],[c_2317,c_459])).

tff(c_2460,plain,(
    ! [A_432] :
      ( k1_funct_1('#skF_11','#skF_10') = A_432
      | ~ v5_relat_1('#skF_11',k1_tarski(A_432)) ) ),
    inference(resolution,[status(thm)],[c_90,c_2405])).

tff(c_2463,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_260,c_2460])).

tff(c_2467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2463])).

tff(c_2468,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_908])).

tff(c_157,plain,(
    ! [A_99,B_100] : ~ v1_xboole_0(k2_tarski(A_99,B_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_120])).

tff(c_159,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_157])).

tff(c_2499,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2468,c_159])).

tff(c_2504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:12:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.87  
% 4.80/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.87  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 4.80/1.87  
% 4.80/1.87  %Foreground sorts:
% 4.80/1.87  
% 4.80/1.87  
% 4.80/1.87  %Background operators:
% 4.80/1.87  
% 4.80/1.87  
% 4.80/1.87  %Foreground operators:
% 4.80/1.87  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.80/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.80/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/1.87  tff('#skF_11', type, '#skF_11': $i).
% 4.80/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.80/1.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.80/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.80/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.80/1.87  tff('#skF_10', type, '#skF_10': $i).
% 4.80/1.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.80/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.80/1.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.80/1.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.80/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.80/1.87  tff('#skF_9', type, '#skF_9': $i).
% 4.80/1.87  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.80/1.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.80/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.80/1.87  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.80/1.87  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.80/1.87  tff('#skF_8', type, '#skF_8': $i).
% 4.80/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.80/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.80/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.80/1.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.80/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.80/1.87  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.80/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.80/1.87  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.80/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.80/1.87  
% 4.80/1.89  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.80/1.89  tff(f_133, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 4.80/1.89  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.80/1.89  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.80/1.89  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.80/1.89  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.80/1.89  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.80/1.89  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 4.80/1.89  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.80/1.89  tff(f_69, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.80/1.89  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.80/1.89  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.80/1.89  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.80/1.89  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.80/1.89  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.80/1.89  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.80/1.89  tff(c_88, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.80/1.89  tff(c_92, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.80/1.89  tff(c_251, plain, (![C_130, B_131, A_132]: (v5_relat_1(C_130, B_131) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.80/1.89  tff(c_260, plain, (v5_relat_1('#skF_11', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_92, c_251])).
% 4.80/1.89  tff(c_90, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.80/1.89  tff(c_189, plain, (![C_109, A_110, B_111]: (v1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.80/1.89  tff(c_198, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_92, c_189])).
% 4.80/1.89  tff(c_96, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.80/1.89  tff(c_94, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.80/1.89  tff(c_388, plain, (![A_170, B_171, C_172]: (k1_relset_1(A_170, B_171, C_172)=k1_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.80/1.89  tff(c_402, plain, (k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_92, c_388])).
% 4.80/1.89  tff(c_892, plain, (![B_254, A_255, C_256]: (k1_xboole_0=B_254 | k1_relset_1(A_255, B_254, C_256)=A_255 | ~v1_funct_2(C_256, A_255, B_254) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_254))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.80/1.89  tff(c_903, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_92, c_892])).
% 4.80/1.89  tff(c_908, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_402, c_903])).
% 4.80/1.89  tff(c_909, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_908])).
% 4.80/1.89  tff(c_48, plain, (![B_26, A_25]: (r1_tarski(k2_relat_1(B_26), A_25) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.80/1.89  tff(c_597, plain, (![A_196, D_197]: (r2_hidden(k1_funct_1(A_196, D_197), k2_relat_1(A_196)) | ~r2_hidden(D_197, k1_relat_1(A_196)) | ~v1_funct_1(A_196) | ~v1_relat_1(A_196))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.80/1.89  tff(c_42, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.80/1.89  tff(c_261, plain, (![A_133, C_134, B_135]: (m1_subset_1(A_133, C_134) | ~m1_subset_1(B_135, k1_zfmisc_1(C_134)) | ~r2_hidden(A_133, B_135))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.80/1.89  tff(c_266, plain, (![A_133, B_21, A_20]: (m1_subset_1(A_133, B_21) | ~r2_hidden(A_133, A_20) | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_42, c_261])).
% 4.80/1.89  tff(c_2267, plain, (![A_422, D_423, B_424]: (m1_subset_1(k1_funct_1(A_422, D_423), B_424) | ~r1_tarski(k2_relat_1(A_422), B_424) | ~r2_hidden(D_423, k1_relat_1(A_422)) | ~v1_funct_1(A_422) | ~v1_relat_1(A_422))), inference(resolution, [status(thm)], [c_597, c_266])).
% 4.80/1.89  tff(c_2271, plain, (![B_425, D_426, A_427]: (m1_subset_1(k1_funct_1(B_425, D_426), A_427) | ~r2_hidden(D_426, k1_relat_1(B_425)) | ~v1_funct_1(B_425) | ~v5_relat_1(B_425, A_427) | ~v1_relat_1(B_425))), inference(resolution, [status(thm)], [c_48, c_2267])).
% 4.80/1.89  tff(c_2292, plain, (![D_426, A_427]: (m1_subset_1(k1_funct_1('#skF_11', D_426), A_427) | ~r2_hidden(D_426, '#skF_8') | ~v1_funct_1('#skF_11') | ~v5_relat_1('#skF_11', A_427) | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_909, c_2271])).
% 4.80/1.89  tff(c_2317, plain, (![D_428, A_429]: (m1_subset_1(k1_funct_1('#skF_11', D_428), A_429) | ~r2_hidden(D_428, '#skF_8') | ~v5_relat_1('#skF_11', A_429))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_96, c_2292])).
% 4.80/1.89  tff(c_32, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.80/1.89  tff(c_137, plain, (![A_97, B_98]: (k1_enumset1(A_97, A_97, B_98)=k2_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.80/1.89  tff(c_116, plain, (![E_83, A_84, B_85]: (r2_hidden(E_83, k1_enumset1(A_84, B_85, E_83)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.80/1.89  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.80/1.89  tff(c_120, plain, (![A_84, B_85, E_83]: (~v1_xboole_0(k1_enumset1(A_84, B_85, E_83)))), inference(resolution, [status(thm)], [c_116, c_2])).
% 4.80/1.89  tff(c_148, plain, (![A_97, B_98]: (~v1_xboole_0(k2_tarski(A_97, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_120])).
% 4.80/1.89  tff(c_38, plain, (![A_18, B_19]: (r2_hidden(A_18, B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.80/1.89  tff(c_34, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.80/1.89  tff(c_322, plain, (![E_156, C_157, B_158, A_159]: (E_156=C_157 | E_156=B_158 | E_156=A_159 | ~r2_hidden(E_156, k1_enumset1(A_159, B_158, C_157)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.80/1.89  tff(c_424, plain, (![E_178, B_179, A_180]: (E_178=B_179 | E_178=A_180 | E_178=A_180 | ~r2_hidden(E_178, k2_tarski(A_180, B_179)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_322])).
% 4.80/1.89  tff(c_428, plain, (![B_179, A_18, A_180]: (B_179=A_18 | A_180=A_18 | v1_xboole_0(k2_tarski(A_180, B_179)) | ~m1_subset_1(A_18, k2_tarski(A_180, B_179)))), inference(resolution, [status(thm)], [c_38, c_424])).
% 4.80/1.89  tff(c_452, plain, (![B_181, A_182, A_183]: (B_181=A_182 | A_183=A_182 | ~m1_subset_1(A_182, k2_tarski(A_183, B_181)))), inference(negUnitSimplification, [status(thm)], [c_148, c_428])).
% 4.80/1.89  tff(c_459, plain, (![A_182, A_12]: (A_182=A_12 | A_182=A_12 | ~m1_subset_1(A_182, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_452])).
% 4.80/1.89  tff(c_2405, plain, (![D_430, A_431]: (k1_funct_1('#skF_11', D_430)=A_431 | ~r2_hidden(D_430, '#skF_8') | ~v5_relat_1('#skF_11', k1_tarski(A_431)))), inference(resolution, [status(thm)], [c_2317, c_459])).
% 4.80/1.89  tff(c_2460, plain, (![A_432]: (k1_funct_1('#skF_11', '#skF_10')=A_432 | ~v5_relat_1('#skF_11', k1_tarski(A_432)))), inference(resolution, [status(thm)], [c_90, c_2405])).
% 4.80/1.89  tff(c_2463, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_260, c_2460])).
% 4.80/1.89  tff(c_2467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_2463])).
% 4.80/1.89  tff(c_2468, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_908])).
% 4.80/1.89  tff(c_157, plain, (![A_99, B_100]: (~v1_xboole_0(k2_tarski(A_99, B_100)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_120])).
% 4.80/1.89  tff(c_159, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_157])).
% 4.80/1.89  tff(c_2499, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2468, c_159])).
% 4.80/1.89  tff(c_2504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2499])).
% 4.80/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.89  
% 4.80/1.89  Inference rules
% 4.80/1.89  ----------------------
% 4.80/1.89  #Ref     : 0
% 4.80/1.89  #Sup     : 521
% 4.80/1.89  #Fact    : 2
% 4.80/1.89  #Define  : 0
% 4.80/1.89  #Split   : 5
% 4.80/1.89  #Chain   : 0
% 4.80/1.89  #Close   : 0
% 4.80/1.89  
% 4.80/1.89  Ordering : KBO
% 4.80/1.89  
% 4.80/1.89  Simplification rules
% 4.80/1.89  ----------------------
% 4.80/1.89  #Subsume      : 76
% 4.80/1.89  #Demod        : 82
% 4.80/1.89  #Tautology    : 61
% 4.80/1.89  #SimpNegUnit  : 34
% 4.80/1.89  #BackRed      : 7
% 4.80/1.89  
% 4.80/1.89  #Partial instantiations: 0
% 4.80/1.89  #Strategies tried      : 1
% 4.80/1.89  
% 4.80/1.89  Timing (in seconds)
% 4.80/1.89  ----------------------
% 4.80/1.89  Preprocessing        : 0.36
% 4.80/1.89  Parsing              : 0.18
% 4.80/1.89  CNF conversion       : 0.03
% 4.80/1.89  Main loop            : 0.76
% 4.80/1.89  Inferencing          : 0.28
% 4.80/1.89  Reduction            : 0.21
% 4.80/1.89  Demodulation         : 0.14
% 4.80/1.89  BG Simplification    : 0.04
% 4.80/1.89  Subsumption          : 0.17
% 4.80/1.89  Abstraction          : 0.05
% 4.80/1.89  MUC search           : 0.00
% 4.80/1.89  Cooper               : 0.00
% 4.80/1.89  Total                : 1.15
% 4.80/1.89  Index Insertion      : 0.00
% 4.80/1.89  Index Deletion       : 0.00
% 4.80/1.89  Index Matching       : 0.00
% 4.80/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
