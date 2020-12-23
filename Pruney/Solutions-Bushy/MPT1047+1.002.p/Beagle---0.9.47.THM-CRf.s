%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1047+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:19 EST 2020

% Result     : Theorem 52.56s
% Output     : CNFRefutation 52.73s
% Verified   : 
% Statistics : Number of formulae       :  300 (72674 expanded)
%              Number of leaves         :   37 (25254 expanded)
%              Depth                    :   42
%              Number of atoms          :  883 (282458 expanded)
%              Number of equality atoms :  205 (42340 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_6 > #skF_7 > #skF_10 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,k1_tarski(B))
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
           => k5_partfun1(A,k1_tarski(B),C) = k1_tarski(D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
         => r1_partfun1(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_partfun1(A,B)
       => r1_partfun1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_partfun1)).

tff(f_73,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( r2_hidden(D,k5_partfun1(A,B,C))
         => ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

tff(f_142,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,k1_tarski(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,k1_tarski(B))
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
         => r2_relset_1(A,k1_tarski(B),C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_78,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') != k1_tarski('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_88,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_80,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_103,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_111,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_80,c_103])).

tff(c_84,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_86,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_110,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_103])).

tff(c_323,plain,(
    ! [C_145,D_146,A_147,B_148] :
      ( r1_partfun1(C_145,D_146)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(A_147,k1_tarski(B_148))))
      | ~ v1_funct_1(D_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_147,k1_tarski(B_148))))
      | ~ v1_funct_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_331,plain,(
    ! [C_145] :
      ( r1_partfun1(C_145,'#skF_9')
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_145) ) ),
    inference(resolution,[status(thm)],[c_86,c_323])).

tff(c_342,plain,(
    ! [C_149] :
      ( r1_partfun1(C_149,'#skF_9')
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_331])).

tff(c_356,plain,
    ( r1_partfun1('#skF_10','#skF_9')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_80,c_342])).

tff(c_364,plain,(
    r1_partfun1('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_356])).

tff(c_62,plain,(
    ! [B_61,A_60] :
      ( r1_partfun1(B_61,A_60)
      | ~ r1_partfun1(A_60,B_61)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_384,plain,
    ( r1_partfun1('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_364,c_62])).

tff(c_387,plain,(
    r1_partfun1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_84,c_110,c_88,c_384])).

tff(c_56,plain,(
    ! [A_55] : ~ v1_xboole_0(k1_tarski(A_55)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_82,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_257,plain,(
    ! [C_127,A_128,B_129] :
      ( v1_partfun1(C_127,A_128)
      | ~ v1_funct_2(C_127,A_128,B_129)
      | ~ v1_funct_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | v1_xboole_0(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_271,plain,
    ( v1_partfun1('#skF_10','#skF_7')
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_10')
    | v1_xboole_0(k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_80,c_257])).

tff(c_280,plain,
    ( v1_partfun1('#skF_10','#skF_7')
    | v1_xboole_0(k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_271])).

tff(c_281,plain,(
    v1_partfun1('#skF_10','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_280])).

tff(c_1298,plain,(
    ! [F_221,A_222,B_223,C_224] :
      ( r2_hidden(F_221,k5_partfun1(A_222,B_223,C_224))
      | ~ r1_partfun1(C_224,F_221)
      | ~ v1_partfun1(F_221,A_222)
      | ~ m1_subset_1(F_221,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ v1_funct_1(F_221)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ v1_funct_1(C_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1329,plain,(
    ! [C_224] :
      ( r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_224))
      | ~ r1_partfun1(C_224,'#skF_10')
      | ~ v1_partfun1('#skF_10','#skF_7')
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_224) ) ),
    inference(resolution,[status(thm)],[c_80,c_1298])).

tff(c_1345,plain,(
    ! [C_225] :
      ( r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_225))
      | ~ r1_partfun1(C_225,'#skF_10')
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_281,c_1329])).

tff(c_1384,plain,
    ( r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | ~ r1_partfun1('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_1345])).

tff(c_1399,plain,(
    r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_387,c_1384])).

tff(c_2053,plain,(
    ! [A_255,B_256,C_257,D_258] :
      ( m1_subset_1('#skF_4'(A_255,B_256,C_257,D_258),k1_zfmisc_1(k2_zfmisc_1(A_255,B_256)))
      | r2_hidden('#skF_5'(A_255,B_256,C_257,D_258),D_258)
      | k5_partfun1(A_255,B_256,C_257) = D_258
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256)))
      | ~ v1_funct_1(C_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2145,plain,(
    ! [A_259,B_260,C_261,D_262] :
      ( v1_relat_1('#skF_4'(A_259,B_260,C_261,D_262))
      | r2_hidden('#skF_5'(A_259,B_260,C_261,D_262),D_262)
      | k5_partfun1(A_259,B_260,C_261) = D_262
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260)))
      | ~ v1_funct_1(C_261) ) ),
    inference(resolution,[status(thm)],[c_2053,c_2])).

tff(c_2187,plain,(
    ! [D_262] :
      ( v1_relat_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_262))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_262),D_262)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_262
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_86,c_2145])).

tff(c_2206,plain,(
    ! [D_262] :
      ( v1_relat_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_262))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_262),D_262)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_262 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2187])).

tff(c_512,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( v1_funct_1('#skF_4'(A_182,B_183,C_184,D_185))
      | r2_hidden('#skF_5'(A_182,B_183,C_184,D_185),D_185)
      | k5_partfun1(A_182,B_183,C_184) = D_185
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_520,plain,(
    ! [D_185] :
      ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_185))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_185),D_185)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_185
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_86,c_512])).

tff(c_531,plain,(
    ! [D_186] :
      ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_186))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_186),D_186)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_186 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_520])).

tff(c_26,plain,(
    ! [E_51,B_14,A_13,C_15] :
      ( '#skF_6'(E_51,B_14,k5_partfun1(A_13,B_14,C_15),A_13,C_15) = E_51
      | ~ r2_hidden(E_51,k5_partfun1(A_13,B_14,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_13986,plain,(
    ! [A_1158,B_1159,C_1160] :
      ( '#skF_6'('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1(A_1158,B_1159,C_1160)),B_1159,k5_partfun1(A_1158,B_1159,C_1160),A_1158,C_1160) = '#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1(A_1158,B_1159,C_1160))
      | ~ m1_subset_1(C_1160,k1_zfmisc_1(k2_zfmisc_1(A_1158,B_1159)))
      | ~ v1_funct_1(C_1160)
      | v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1(A_1158,B_1159,C_1160)))
      | k5_partfun1(A_1158,B_1159,C_1160) = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_531,c_26])).

tff(c_1490,plain,(
    ! [E_226,B_227,A_228,C_229] :
      ( m1_subset_1('#skF_6'(E_226,B_227,k5_partfun1(A_228,B_227,C_229),A_228,C_229),k1_zfmisc_1(k2_zfmisc_1(A_228,B_227)))
      | ~ r2_hidden(E_226,k5_partfun1(A_228,B_227,C_229))
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_228,B_227)))
      | ~ v1_funct_1(C_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1558,plain,(
    ! [E_230,B_231,A_232,C_233] :
      ( v1_relat_1('#skF_6'(E_230,B_231,k5_partfun1(A_232,B_231,C_233),A_232,C_233))
      | ~ r2_hidden(E_230,k5_partfun1(A_232,B_231,C_233))
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_232,B_231)))
      | ~ v1_funct_1(C_233) ) ),
    inference(resolution,[status(thm)],[c_1490,c_2])).

tff(c_1591,plain,(
    ! [E_230] :
      ( v1_relat_1('#skF_6'(E_230,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_230,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_80,c_1558])).

tff(c_1607,plain,(
    ! [E_230] :
      ( v1_relat_1('#skF_6'(E_230,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_230,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1591])).

tff(c_14070,plain,
    ( v1_relat_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10')
    | v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_13986,c_1607])).

tff(c_14104,plain,
    ( v1_relat_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_14070])).

tff(c_14117,plain,(
    ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_14104])).

tff(c_14181,plain,
    ( v1_relat_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_2206,c_14117])).

tff(c_14189,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_14181])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( '#skF_1'(A_8,B_9) = A_8
      | r2_hidden('#skF_2'(A_8,B_9),B_9)
      | k1_tarski(A_8) = B_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_282,plain,(
    ! [D_130,A_131,B_132,C_133] :
      ( v1_funct_2(D_130,A_131,B_132)
      | ~ r2_hidden(D_130,k5_partfun1(A_131,B_132,C_133))
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_293,plain,(
    ! [A_8,A_131,B_132,C_133] :
      ( v1_funct_2('#skF_2'(A_8,k5_partfun1(A_131,B_132,C_133)),A_131,B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(C_133)
      | '#skF_1'(A_8,k5_partfun1(A_131,B_132,C_133)) = A_8
      | k5_partfun1(A_131,B_132,C_133) = k1_tarski(A_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_282])).

tff(c_14636,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | '#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = A_8
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14189,c_293])).

tff(c_14877,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_8
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14189,c_14189,c_84,c_80,c_14636])).

tff(c_309,plain,(
    ! [D_138,A_139,B_140,C_141] :
      ( m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ r2_hidden(D_138,k5_partfun1(A_139,B_140,C_141))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_320,plain,(
    ! [A_8,A_139,B_140,C_141] :
      ( m1_subset_1('#skF_2'(A_8,k5_partfun1(A_139,B_140,C_141)),k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_1(C_141)
      | '#skF_1'(A_8,k5_partfun1(A_139,B_140,C_141)) = A_8
      | k5_partfun1(A_139,B_140,C_141) = k1_tarski(A_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_309])).

tff(c_14627,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | '#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = A_8
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14189,c_320])).

tff(c_14871,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | '#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_8
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14189,c_14189,c_84,c_80,c_14627])).

tff(c_442,plain,(
    ! [E_159,B_160,A_161,C_162] :
      ( v1_funct_1('#skF_6'(E_159,B_160,k5_partfun1(A_161,B_160,C_162),A_161,C_162))
      | ~ r2_hidden(E_159,k5_partfun1(A_161,B_160,C_162))
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160)))
      | ~ v1_funct_1(C_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_452,plain,(
    ! [E_159] :
      ( v1_funct_1('#skF_6'(E_159,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_159,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_80,c_442])).

tff(c_460,plain,(
    ! [E_159] :
      ( v1_funct_1('#skF_6'(E_159,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_159,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_452])).

tff(c_14309,plain,(
    ! [E_159] :
      ( v1_funct_1('#skF_6'(E_159,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_159,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14189,c_14189,c_460])).

tff(c_14647,plain,(
    ! [E_51] :
      ( '#skF_6'(E_51,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10') = E_51
      | ~ r2_hidden(E_51,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14189,c_26])).

tff(c_14885,plain,(
    ! [E_51] :
      ( '#skF_6'(E_51,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10') = E_51
      | ~ r2_hidden(E_51,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_14189,c_14647])).

tff(c_28,plain,(
    ! [E_51,B_14,A_13,C_15] :
      ( m1_subset_1('#skF_6'(E_51,B_14,k5_partfun1(A_13,B_14,C_15),A_13,C_15),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ r2_hidden(E_51,k5_partfun1(A_13,B_14,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14639,plain,(
    ! [E_51] :
      ( m1_subset_1('#skF_6'(E_51,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(E_51,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14189,c_28])).

tff(c_20330,plain,(
    ! [E_1229] :
      ( m1_subset_1('#skF_6'(E_1229,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(E_1229,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_14189,c_14639])).

tff(c_2446,plain,(
    ! [A_269,B_270,C_271,D_272] :
      ( r2_relset_1(A_269,k1_tarski(B_270),C_271,D_272)
      | ~ m1_subset_1(D_272,k1_zfmisc_1(k2_zfmisc_1(A_269,k1_tarski(B_270))))
      | ~ v1_funct_2(D_272,A_269,k1_tarski(B_270))
      | ~ v1_funct_1(D_272)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_269,k1_tarski(B_270))))
      | ~ v1_funct_2(C_271,A_269,k1_tarski(B_270))
      | ~ v1_funct_1(C_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2498,plain,(
    ! [C_271] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),C_271,'#skF_10')
      | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2(C_271,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1(C_271) ) ),
    inference(resolution,[status(thm)],[c_80,c_2446])).

tff(c_2520,plain,(
    ! [C_271] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),C_271,'#skF_10')
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2(C_271,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1(C_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_2498])).

tff(c_32724,plain,(
    ! [E_1538] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_6'(E_1538,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'),'#skF_10')
      | ~ v1_funct_2('#skF_6'(E_1538,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'),'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(E_1538,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_1538,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_20330,c_2520])).

tff(c_48101,plain,(
    ! [E_1910] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_1910,'#skF_10')
      | ~ v1_funct_2('#skF_6'(E_1910,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'),'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(E_1910,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_1910,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_1910,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14885,c_32724])).

tff(c_48116,plain,(
    ! [E_1911] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_1911,'#skF_10')
      | ~ v1_funct_2(E_1911,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(E_1911,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_1911,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_1911,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_1911,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14885,c_48101])).

tff(c_48135,plain,(
    ! [E_1912] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_1912,'#skF_10')
      | ~ v1_funct_2(E_1912,'#skF_7',k1_tarski('#skF_8'))
      | ~ r2_hidden(E_1912,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_14309,c_48116])).

tff(c_48530,plain,(
    ! [A_1917] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_2'(A_1917,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_10')
      | ~ v1_funct_2('#skF_2'(A_1917,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_1917,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1917
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1917) ) ),
    inference(resolution,[status(thm)],[c_18,c_48135])).

tff(c_60,plain,(
    ! [D_59,C_58,A_56,B_57] :
      ( D_59 = C_58
      | ~ r2_relset_1(A_56,B_57,C_58,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48532,plain,(
    ! [A_1917] :
      ( '#skF_2'(A_1917,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ m1_subset_1('#skF_2'(A_1917,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2('#skF_2'(A_1917,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_1917,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1917
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1917) ) ),
    inference(resolution,[status(thm)],[c_48530,c_60])).

tff(c_49802,plain,(
    ! [A_1951] :
      ( '#skF_2'(A_1951,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ m1_subset_1('#skF_2'(A_1951,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2('#skF_2'(A_1951,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_1951,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1951
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1951) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_48532])).

tff(c_49829,plain,(
    ! [A_1952] :
      ( '#skF_2'(A_1952,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ v1_funct_2('#skF_2'(A_1952,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_1952,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1952
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1952) ) ),
    inference(resolution,[status(thm)],[c_14871,c_49802])).

tff(c_49849,plain,(
    ! [A_1953] :
      ( '#skF_2'(A_1953,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_1953,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1953
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1953) ) ),
    inference(resolution,[status(thm)],[c_14877,c_49829])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( '#skF_1'(A_8,B_9) = A_8
      | '#skF_2'(A_8,B_9) != A_8
      | k1_tarski(A_8) = B_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50019,plain,(
    ! [A_1953] :
      ( '#skF_1'(A_1953,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1953
      | A_1953 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1953)
      | '#skF_1'(A_1953,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1953
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1953) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49849,c_14])).

tff(c_50362,plain,(
    ! [A_1960] :
      ( A_1960 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1960)
      | '#skF_1'(A_1960,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1960 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_50019])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_1'(A_8,B_9),B_9)
      | '#skF_2'(A_8,B_9) != A_8
      | k1_tarski(A_8) = B_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50818,plain,(
    ! [A_1972] :
      ( ~ r2_hidden(A_1972,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | '#skF_2'(A_1972,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != A_1972
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1972)
      | A_1972 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1972) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50362,c_12])).

tff(c_51083,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(resolution,[status(thm)],[c_1399,c_50818])).

tff(c_51201,plain,(
    '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_78,c_51083])).

tff(c_49844,plain,(
    ! [A_8] :
      ( '#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_8
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_8) ) ),
    inference(resolution,[status(thm)],[c_14877,c_49829])).

tff(c_51271,plain,
    ( '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_49844,c_51201])).

tff(c_51274,plain,(
    '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_51271])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_1'(A_8,B_9),B_9)
      | r2_hidden('#skF_2'(A_8,B_9),B_9)
      | k1_tarski(A_8) = B_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_319,plain,(
    ! [A_8,A_139,B_140,C_141] :
      ( m1_subset_1('#skF_2'(A_8,k5_partfun1(A_139,B_140,C_141)),k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_1(C_141)
      | ~ r2_hidden('#skF_1'(A_8,k5_partfun1(A_139,B_140,C_141)),k5_partfun1(A_139,B_140,C_141))
      | k5_partfun1(A_139,B_140,C_141) = k1_tarski(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_309])).

tff(c_51343,plain,
    ( m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9')
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_51274,c_319])).

tff(c_51438,plain,
    ( m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_88,c_86,c_51343])).

tff(c_51439,plain,(
    m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_51438])).

tff(c_214,plain,(
    ! [D_117,A_118,B_119,C_120] :
      ( v1_funct_1(D_117)
      | ~ r2_hidden(D_117,k5_partfun1(A_118,B_119,C_120))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_224,plain,(
    ! [A_8,A_118,B_119,C_120] :
      ( v1_funct_1('#skF_2'(A_8,k5_partfun1(A_118,B_119,C_120)))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(C_120)
      | ~ r2_hidden('#skF_1'(A_8,k5_partfun1(A_118,B_119,C_120)),k5_partfun1(A_118,B_119,C_120))
      | k5_partfun1(A_118,B_119,C_120) = k1_tarski(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_214])).

tff(c_14633,plain,(
    ! [A_8] :
      ( v1_funct_1('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | ~ r2_hidden('#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14189,c_224])).

tff(c_14875,plain,(
    ! [A_8] :
      ( v1_funct_1('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
      | ~ r2_hidden('#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14189,c_14189,c_84,c_80,c_14189,c_14633])).

tff(c_51329,plain,
    ( v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_51274,c_14875])).

tff(c_51420,plain,
    ( v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_51329])).

tff(c_51421,plain,(
    v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_51420])).

tff(c_292,plain,(
    ! [A_8,A_131,B_132,C_133] :
      ( v1_funct_2('#skF_2'(A_8,k5_partfun1(A_131,B_132,C_133)),A_131,B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(C_133)
      | ~ r2_hidden('#skF_1'(A_8,k5_partfun1(A_131,B_132,C_133)),k5_partfun1(A_131,B_132,C_133))
      | k5_partfun1(A_131,B_132,C_133) = k1_tarski(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_282])).

tff(c_14618,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | ~ r2_hidden('#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14189,c_292])).

tff(c_14865,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14189,c_14189,c_84,c_80,c_14189,c_14618])).

tff(c_51323,plain,
    ( v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_51274,c_14865])).

tff(c_51414,plain,
    ( v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_51323])).

tff(c_51415,plain,(
    v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_51414])).

tff(c_51690,plain,
    ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_10')
    | ~ v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(resolution,[status(thm)],[c_51439,c_2520])).

tff(c_51809,plain,(
    r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51421,c_51415,c_51690])).

tff(c_51874,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(resolution,[status(thm)],[c_51809,c_60])).

tff(c_51880,plain,(
    '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51439,c_80,c_51874])).

tff(c_51882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51201,c_51880])).

tff(c_51884,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') != k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_14181])).

tff(c_1717,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( '#skF_4'(A_241,B_242,C_243,D_244) = '#skF_3'(A_241,B_242,C_243,D_244)
      | r2_hidden('#skF_5'(A_241,B_242,C_243,D_244),D_244)
      | k5_partfun1(A_241,B_242,C_243) = D_244
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242)))
      | ~ v1_funct_1(C_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1751,plain,(
    ! [D_244] :
      ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_244) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_244)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_244),D_244)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_244
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_86,c_1717])).

tff(c_1767,plain,(
    ! [D_244] :
      ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_244) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_244)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_244),D_244)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_244 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1751])).

tff(c_14182,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_1767,c_14117])).

tff(c_51930,plain,(
    '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_51884,c_14182])).

tff(c_51883,plain,(
    v1_relat_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_14181])).

tff(c_51935,plain,(
    v1_relat_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51930,c_51883])).

tff(c_527,plain,(
    ! [D_185] :
      ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_185))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_185),D_185)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_185 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_520])).

tff(c_14186,plain,
    ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_527,c_14117])).

tff(c_51911,plain,(
    v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_51884,c_14186])).

tff(c_51934,plain,(
    v1_funct_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51930,c_51911])).

tff(c_333,plain,(
    ! [C_145] :
      ( r1_partfun1(C_145,'#skF_10')
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_145) ) ),
    inference(resolution,[status(thm)],[c_80,c_323])).

tff(c_341,plain,(
    ! [C_145] :
      ( r1_partfun1(C_145,'#skF_10')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_333])).

tff(c_5149,plain,(
    ! [C_460,D_461] :
      ( r1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),C_460,D_461),'#skF_10')
      | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),C_460,D_461))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),C_460,D_461),D_461)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_460) = D_461
      | ~ m1_subset_1(C_460,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_460) ) ),
    inference(resolution,[status(thm)],[c_2053,c_341])).

tff(c_5230,plain,(
    ! [D_461] :
      ( r1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_461),'#skF_10')
      | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_461))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_461),D_461)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_461
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_86,c_5149])).

tff(c_5262,plain,(
    ! [D_461] :
      ( r1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_461),'#skF_10')
      | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_461))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_461),D_461)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_461 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5230])).

tff(c_14179,plain,
    ( r1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10')
    | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_5262,c_14117])).

tff(c_52363,plain,
    ( r1_partfun1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10')
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51934,c_51930,c_51930,c_14179])).

tff(c_52364,plain,(
    r1_partfun1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_51884,c_52363])).

tff(c_52366,plain,
    ( r1_partfun1('#skF_10','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_funct_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_relat_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_52364,c_62])).

tff(c_52369,plain,(
    r1_partfun1('#skF_10','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51935,c_51934,c_111,c_84,c_52366])).

tff(c_557,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( v1_partfun1('#skF_4'(A_187,B_188,C_189,D_190),A_187)
      | r2_hidden('#skF_5'(A_187,B_188,C_189,D_190),D_190)
      | k5_partfun1(A_187,B_188,C_189) = D_190
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_565,plain,(
    ! [D_190] :
      ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_190),'#skF_7')
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_190),D_190)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_190
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_86,c_557])).

tff(c_572,plain,(
    ! [D_190] :
      ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_190),'#skF_7')
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_190),D_190)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_190 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_565])).

tff(c_14185,plain,
    ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_572,c_14117])).

tff(c_51912,plain,(
    v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_51884,c_14185])).

tff(c_51933,plain,(
    v1_partfun1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51930,c_51912])).

tff(c_52,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( m1_subset_1('#skF_4'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | r2_hidden('#skF_5'(A_13,B_14,C_15,D_37),D_37)
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52072,plain,
    ( m1_subset_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_51930,c_52])).

tff(c_52211,plain,
    ( m1_subset_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_52072])).

tff(c_52212,plain,(
    m1_subset_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_51884,c_14117,c_52211])).

tff(c_20,plain,(
    ! [F_54,A_13,B_14,C_15] :
      ( r2_hidden(F_54,k5_partfun1(A_13,B_14,C_15))
      | ~ r1_partfun1(C_15,F_54)
      | ~ v1_partfun1(F_54,A_13)
      | ~ m1_subset_1(F_54,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(F_54)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52430,plain,(
    ! [C_15] :
      ( r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_15))
      | ~ r1_partfun1(C_15,'#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ v1_partfun1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
      | ~ v1_funct_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_52212,c_20])).

tff(c_53503,plain,(
    ! [C_2014] :
      ( r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_2014))
      | ~ r1_partfun1(C_2014,'#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_2014,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_2014) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51934,c_51933,c_52430])).

tff(c_888,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( ~ r2_hidden('#skF_3'(A_200,B_201,C_202,D_203),D_203)
      | r2_hidden('#skF_5'(A_200,B_201,C_202,D_203),D_203)
      | k5_partfun1(A_200,B_201,C_202) = D_203
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_1(C_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_908,plain,(
    ! [D_203] :
      ( ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_203),D_203)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_203),D_203)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_203
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_86,c_888])).

tff(c_919,plain,(
    ! [D_203] :
      ( ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_203),D_203)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_203),D_203)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_203 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_908])).

tff(c_14184,plain,
    ( ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_919,c_14117])).

tff(c_51924,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_51884,c_14184])).

tff(c_53506,plain,
    ( ~ r1_partfun1('#skF_10','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_53503,c_51924])).

tff(c_53539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_52369,c_53506])).

tff(c_53541,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_14104])).

tff(c_70,plain,(
    ! [D_71,A_67,B_68,C_69] :
      ( v1_funct_1(D_71)
      | ~ r2_hidden(D_71,k5_partfun1(A_67,B_68,C_69))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_53575,plain,
    ( v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_53541,c_70])).

tff(c_53590,plain,(
    v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_53575])).

tff(c_66,plain,(
    ! [D_71,A_67,B_68,C_69] :
      ( m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ r2_hidden(D_71,k5_partfun1(A_67,B_68,C_69))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_53571,plain,
    ( m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_53541,c_66])).

tff(c_53584,plain,(
    m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_53571])).

tff(c_68,plain,(
    ! [D_71,A_67,B_68,C_69] :
      ( v1_funct_2(D_71,A_67,B_68)
      | ~ r2_hidden(D_71,k5_partfun1(A_67,B_68,C_69))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_53573,plain,
    ( v1_funct_2('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_53541,c_68])).

tff(c_53587,plain,(
    v1_funct_2('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_53573])).

tff(c_4,plain,(
    ! [C_7,A_4,B_5] :
      ( v1_partfun1(C_7,A_4)
      | ~ v1_funct_2(C_7,A_4,B_5)
      | ~ v1_funct_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | v1_xboole_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53813,plain,
    ( v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ v1_funct_2('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | v1_xboole_0(k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_53584,c_4])).

tff(c_53929,plain,
    ( v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | v1_xboole_0(k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53590,c_53587,c_53813])).

tff(c_53930,plain,(
    v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_53929])).

tff(c_53932,plain,(
    v1_relat_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_53584,c_2])).

tff(c_338,plain,(
    ! [C_145] :
      ( r1_partfun1(C_145,'#skF_9')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_331])).

tff(c_53808,plain,
    ( r1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_9')
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_53584,c_338])).

tff(c_53923,plain,(
    r1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53590,c_53808])).

tff(c_53939,plain,
    ( r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_relat_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_53923,c_62])).

tff(c_53942,plain,(
    r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53932,c_53590,c_110,c_88,c_53939])).

tff(c_42,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( v1_funct_1('#skF_4'(A_13,B_14,C_15,D_37))
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54095,plain,
    ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_53942,c_42])).

tff(c_54112,plain,
    ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_53590,c_53584,c_53930,c_54095])).

tff(c_54575,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_54112])).

tff(c_55025,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | '#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = A_8
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54575,c_293])).

tff(c_55268,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_8
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54575,c_54575,c_84,c_80,c_55025])).

tff(c_55016,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | '#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = A_8
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54575,c_320])).

tff(c_55262,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | '#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_8
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54575,c_54575,c_84,c_80,c_55016])).

tff(c_54695,plain,(
    ! [E_159] :
      ( v1_funct_1('#skF_6'(E_159,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_159,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54575,c_54575,c_460])).

tff(c_55036,plain,(
    ! [E_51] :
      ( '#skF_6'(E_51,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),'#skF_7','#skF_10') = E_51
      | ~ r2_hidden(E_51,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54575,c_26])).

tff(c_55276,plain,(
    ! [E_51] :
      ( '#skF_6'(E_51,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10') = E_51
      | ~ r2_hidden(E_51,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_54575,c_55036])).

tff(c_55028,plain,(
    ! [E_51] :
      ( m1_subset_1('#skF_6'(E_51,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(E_51,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54575,c_28])).

tff(c_61705,plain,(
    ! [E_2102] :
      ( m1_subset_1('#skF_6'(E_2102,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(E_2102,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_54575,c_55028])).

tff(c_73197,plain,(
    ! [E_2389] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_6'(E_2389,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'),'#skF_10')
      | ~ v1_funct_2('#skF_6'(E_2389,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'),'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(E_2389,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_2389,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_61705,c_2520])).

tff(c_90578,plain,(
    ! [E_2800] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_2800,'#skF_10')
      | ~ v1_funct_2('#skF_6'(E_2800,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'),'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(E_2800,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_2800,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_2800,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55276,c_73197])).

tff(c_90593,plain,(
    ! [E_2801] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_2801,'#skF_10')
      | ~ v1_funct_2(E_2801,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(E_2801,k1_tarski('#skF_8'),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_2801,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_2801,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_2801,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55276,c_90578])).

tff(c_90612,plain,(
    ! [E_2802] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_2802,'#skF_10')
      | ~ v1_funct_2(E_2802,'#skF_7',k1_tarski('#skF_8'))
      | ~ r2_hidden(E_2802,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_54695,c_90593])).

tff(c_91026,plain,(
    ! [A_2803] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_2'(A_2803,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_10')
      | ~ v1_funct_2('#skF_2'(A_2803,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_2803,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2803
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2803) ) ),
    inference(resolution,[status(thm)],[c_18,c_90612])).

tff(c_91028,plain,(
    ! [A_2803] :
      ( '#skF_2'(A_2803,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ m1_subset_1('#skF_2'(A_2803,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2('#skF_2'(A_2803,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_2803,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2803
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2803) ) ),
    inference(resolution,[status(thm)],[c_91026,c_60])).

tff(c_91951,plain,(
    ! [A_2836] :
      ( '#skF_2'(A_2836,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ m1_subset_1('#skF_2'(A_2836,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2('#skF_2'(A_2836,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_2836,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2836
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2836) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_91028])).

tff(c_91978,plain,(
    ! [A_2837] :
      ( '#skF_2'(A_2837,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ v1_funct_2('#skF_2'(A_2837,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_2837,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2837
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2837) ) ),
    inference(resolution,[status(thm)],[c_55262,c_91951])).

tff(c_91998,plain,(
    ! [A_2838] :
      ( '#skF_2'(A_2838,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_2838,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2838
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2838) ) ),
    inference(resolution,[status(thm)],[c_55268,c_91978])).

tff(c_92174,plain,(
    ! [A_2838] :
      ( '#skF_1'(A_2838,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2838
      | A_2838 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2838)
      | '#skF_1'(A_2838,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2838
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2838) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91998,c_14])).

tff(c_92445,plain,(
    ! [A_2848] :
      ( A_2848 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2848)
      | '#skF_1'(A_2848,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2848 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_92174])).

tff(c_92728,plain,(
    ! [A_2857] :
      ( ~ r2_hidden(A_2857,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | '#skF_2'(A_2857,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != A_2857
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2857)
      | A_2857 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2857) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92445,c_12])).

tff(c_92995,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(resolution,[status(thm)],[c_1399,c_92728])).

tff(c_93128,plain,(
    '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_78,c_92995])).

tff(c_91993,plain,(
    ! [A_8] :
      ( '#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_8
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_8) ) ),
    inference(resolution,[status(thm)],[c_55268,c_91978])).

tff(c_93155,plain,
    ( '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_91993,c_93128])).

tff(c_93158,plain,(
    '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_93155])).

tff(c_93227,plain,
    ( m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9')
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_93158,c_319])).

tff(c_93322,plain,
    ( m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_88,c_86,c_93227])).

tff(c_93323,plain,(
    m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_93322])).

tff(c_55022,plain,(
    ! [A_8] :
      ( v1_funct_1('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | ~ r2_hidden('#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54575,c_224])).

tff(c_55266,plain,(
    ! [A_8] :
      ( v1_funct_1('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
      | ~ r2_hidden('#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54575,c_54575,c_84,c_80,c_54575,c_55022])).

tff(c_93213,plain,
    ( v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_93158,c_55266])).

tff(c_93304,plain,
    ( v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_93213])).

tff(c_93305,plain,(
    v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_93304])).

tff(c_55007,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | ~ r2_hidden('#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54575,c_292])).

tff(c_55256,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_2'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_8,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54575,c_54575,c_84,c_80,c_54575,c_55007])).

tff(c_93204,plain,
    ( v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_93158,c_55256])).

tff(c_93295,plain,
    ( v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_93204])).

tff(c_93296,plain,(
    v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_93295])).

tff(c_93673,plain,
    ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_10')
    | ~ v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(resolution,[status(thm)],[c_93323,c_2520])).

tff(c_93792,plain,(
    r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93305,c_93296,c_93673])).

tff(c_93857,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(resolution,[status(thm)],[c_93792,c_60])).

tff(c_93863,plain,(
    '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93323,c_80,c_93857])).

tff(c_93865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93128,c_93863])).

tff(c_93867,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') != k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_54112])).

tff(c_53771,plain,
    ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10')
    | ~ v1_funct_2('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_53584,c_2520])).

tff(c_53872,plain,(
    r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53590,c_53587,c_53771])).

tff(c_54265,plain,
    ( '#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(resolution,[status(thm)],[c_53872,c_60])).

tff(c_54268,plain,(
    '#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53584,c_80,c_54265])).

tff(c_38,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( '#skF_4'(A_13,B_14,C_15,D_37) = '#skF_3'(A_13,B_14,C_15,D_37)
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54426,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | ~ r1_partfun1('#skF_9','#skF_10')
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_54268,c_38])).

tff(c_54552,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_54268,c_80,c_54268,c_281,c_54268,c_387,c_54426])).

tff(c_95301,plain,(
    '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_93867,c_54552])).

tff(c_93866,plain,(
    v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_54112])).

tff(c_34,plain,(
    ! [C_15,A_13,B_14,D_37] :
      ( r1_partfun1(C_15,'#skF_4'(A_13,B_14,C_15,D_37))
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54430,plain,
    ( r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_54268,c_34])).

tff(c_54556,plain,
    ( r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_54268,c_80,c_281,c_54268,c_387,c_54268,c_54430])).

tff(c_94020,plain,(
    r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_93867,c_54556])).

tff(c_94022,plain,
    ( r1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_9')
    | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_relat_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_94020,c_62])).

tff(c_94025,plain,
    ( r1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_9')
    | ~ v1_relat_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_88,c_93866,c_94022])).

tff(c_94149,plain,(
    ~ v1_relat_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_94025])).

tff(c_40,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( m1_subset_1('#skF_4'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54091,plain,
    ( m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_53942,c_40])).

tff(c_54106,plain,
    ( m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_53590,c_53584,c_53930,c_54091])).

tff(c_94322,plain,(
    m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_93867,c_54106])).

tff(c_94404,plain,(
    v1_relat_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_94322,c_2])).

tff(c_94518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94149,c_94404])).

tff(c_94520,plain,(
    v1_relat_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_94025])).

tff(c_94527,plain,(
    m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_93867,c_54106])).

tff(c_94596,plain,
    ( r1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10')
    | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_94527,c_341])).

tff(c_94708,plain,(
    r1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93866,c_94596])).

tff(c_94749,plain,
    ( r1_partfun1('#skF_10','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_relat_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_94708,c_62])).

tff(c_94752,plain,(
    r1_partfun1('#skF_10','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94520,c_93866,c_111,c_84,c_94749])).

tff(c_95308,plain,(
    r1_partfun1('#skF_10','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95301,c_94752])).

tff(c_95315,plain,(
    v1_funct_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95301,c_93866])).

tff(c_36,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( v1_partfun1('#skF_4'(A_13,B_14,C_15,D_37),A_13)
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54432,plain,
    ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ r1_partfun1('#skF_9','#skF_10')
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_54268,c_36])).

tff(c_54558,plain,
    ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_54268,c_80,c_54268,c_281,c_54268,c_387,c_54432])).

tff(c_94019,plain,(
    v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_93867,c_54558])).

tff(c_95314,plain,(
    v1_partfun1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95301,c_94019])).

tff(c_95310,plain,(
    m1_subset_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95301,c_94527])).

tff(c_96100,plain,(
    ! [C_15] :
      ( r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_15))
      | ~ r1_partfun1(C_15,'#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ v1_partfun1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
      | ~ v1_funct_1('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_95310,c_20])).

tff(c_96760,plain,(
    ! [C_2914] :
      ( r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_2914))
      | ~ r1_partfun1(C_2914,'#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1(C_2914,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_2914) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95315,c_95314,c_96100])).

tff(c_32,plain,(
    ! [A_13,B_14,C_15,D_37] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14,C_15,D_37),D_37)
      | ~ r1_partfun1(C_15,'#skF_5'(A_13,B_14,C_15,D_37))
      | ~ v1_partfun1('#skF_5'(A_13,B_14,C_15,D_37),A_13)
      | ~ m1_subset_1('#skF_5'(A_13,B_14,C_15,D_37),k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1('#skF_5'(A_13,B_14,C_15,D_37))
      | k5_partfun1(A_13,B_14,C_15) = D_37
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_96774,plain,
    ( ~ r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9')
    | ~ r1_partfun1('#skF_10','#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_96760,c_32])).

tff(c_96804,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_95308,c_88,c_86,c_84,c_54268,c_80,c_54268,c_281,c_54268,c_387,c_54268,c_96774])).

tff(c_96806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93867,c_96804])).

%------------------------------------------------------------------------------
