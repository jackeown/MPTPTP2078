%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:31 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 157 expanded)
%              Number of leaves         :   46 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  156 ( 312 expanded)
%              Number of equality atoms :   73 ( 133 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_128,axiom,(
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

tff(c_77,plain,(
    ! [A_54] : k2_tarski(A_54,A_54) = k1_tarski(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_12,B_13] : ~ v1_xboole_0(k2_tarski(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [A_54] : ~ v1_xboole_0(k1_tarski(A_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_14])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_536,plain,(
    ! [A_164,B_165,C_166] :
      ( r2_hidden('#skF_2'(A_164,B_165,C_166),B_165)
      | k1_relset_1(B_165,A_164,C_166) = B_165
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(B_165,A_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_539,plain,
    ( r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_4'),'#skF_6'),k1_tarski('#skF_4'))
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_536])).

tff(c_551,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_539])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_139,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_135])).

tff(c_32,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_146,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_139,c_32])).

tff(c_148,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_193,plain,(
    ! [B_94,A_95] :
      ( k1_tarski(k1_funct_1(B_94,A_95)) = k2_relat_1(B_94)
      | k1_tarski(A_95) != k1_relat_1(B_94)
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_182,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_186,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_182])).

tff(c_64,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_187,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_64])).

tff(c_199,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_187])).

tff(c_220,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_72,c_199])).

tff(c_175,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_179,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_175])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,(
    ! [B_107,C_108,A_109] :
      ( k2_tarski(B_107,C_108) = A_109
      | k1_tarski(C_108) = A_109
      | k1_tarski(B_107) = A_109
      | k1_xboole_0 = A_109
      | ~ r1_tarski(A_109,k2_tarski(B_107,C_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_254,plain,(
    ! [A_6,A_109] :
      ( k2_tarski(A_6,A_6) = A_109
      | k1_tarski(A_6) = A_109
      | k1_tarski(A_6) = A_109
      | k1_xboole_0 = A_109
      | ~ r1_tarski(A_109,k1_tarski(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_238])).

tff(c_269,plain,(
    ! [A_110,A_111] :
      ( k1_tarski(A_110) = A_111
      | k1_tarski(A_110) = A_111
      | k1_tarski(A_110) = A_111
      | k1_xboole_0 = A_111
      | ~ r1_tarski(A_111,k1_tarski(A_110)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_254])).

tff(c_293,plain,(
    ! [A_112,B_113] :
      ( k1_tarski(A_112) = k1_relat_1(B_113)
      | k1_relat_1(B_113) = k1_xboole_0
      | ~ v4_relat_1(B_113,k1_tarski(A_112))
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_28,c_269])).

tff(c_299,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_179,c_293])).

tff(c_302,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_299])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_220,c_302])).

tff(c_305,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_310,plain,(
    ! [A_5] : r1_tarski('#skF_6',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_6])).

tff(c_569,plain,(
    ! [D_178,A_179,B_180,C_181] :
      ( r2_hidden(k4_tarski(D_178,'#skF_3'(A_179,B_180,C_181,D_178)),C_181)
      | ~ r2_hidden(D_178,B_180)
      | k1_relset_1(B_180,A_179,C_181) != B_180
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(B_180,A_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_590,plain,(
    ! [C_186,D_187,A_188,B_189] :
      ( ~ r1_tarski(C_186,k4_tarski(D_187,'#skF_3'(A_188,B_189,C_186,D_187)))
      | ~ r2_hidden(D_187,B_189)
      | k1_relset_1(B_189,A_188,C_186) != B_189
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(B_189,A_188))) ) ),
    inference(resolution,[status(thm)],[c_569,c_36])).

tff(c_601,plain,(
    ! [D_190,B_191,A_192] :
      ( ~ r2_hidden(D_190,B_191)
      | k1_relset_1(B_191,A_192,'#skF_6') != B_191
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_191,A_192))) ) ),
    inference(resolution,[status(thm)],[c_310,c_590])).

tff(c_608,plain,(
    ! [A_193,A_194] :
      ( k1_relset_1(A_193,A_194,'#skF_6') != A_193
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_193,A_194)))
      | v1_xboole_0(A_193) ) ),
    inference(resolution,[status(thm)],[c_4,c_601])).

tff(c_611,plain,
    ( k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_608])).

tff(c_614,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_611])).

tff(c_616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_614])).

tff(c_618,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_539])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_311,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_66])).

tff(c_70,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_62,plain,(
    ! [B_47,A_46,C_48] :
      ( k1_xboole_0 = B_47
      | k1_relset_1(A_46,B_47,C_48) = A_46
      | ~ v1_funct_2(C_48,A_46,B_47)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_628,plain,(
    ! [B_195,A_196,C_197] :
      ( B_195 = '#skF_6'
      | k1_relset_1(A_196,B_195,C_197) = A_196
      | ~ v1_funct_2(C_197,A_196,B_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_62])).

tff(c_631,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_628])).

tff(c_634,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_631])).

tff(c_636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_618,c_311,c_634])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.42  
% 2.93/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.93/1.42  
% 2.93/1.42  %Foreground sorts:
% 2.93/1.42  
% 2.93/1.42  
% 2.93/1.42  %Background operators:
% 2.93/1.42  
% 2.93/1.42  
% 2.93/1.42  %Foreground operators:
% 2.93/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.93/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.93/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.93/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.93/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.93/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.93/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.93/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.93/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.93/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.93/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.93/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.93/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.93/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.93/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.93/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.93/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.93/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.42  
% 2.93/1.44  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.93/1.44  tff(f_42, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 2.93/1.44  tff(f_140, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.93/1.44  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 2.93/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.93/1.44  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.93/1.44  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.93/1.44  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.93/1.44  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.93/1.44  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.93/1.44  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.93/1.44  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.93/1.44  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.93/1.44  tff(f_84, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.93/1.44  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.93/1.44  tff(c_77, plain, (![A_54]: (k2_tarski(A_54, A_54)=k1_tarski(A_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.44  tff(c_14, plain, (![A_12, B_13]: (~v1_xboole_0(k2_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.93/1.44  tff(c_82, plain, (![A_54]: (~v1_xboole_0(k1_tarski(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_14])).
% 2.93/1.44  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.93/1.44  tff(c_536, plain, (![A_164, B_165, C_166]: (r2_hidden('#skF_2'(A_164, B_165, C_166), B_165) | k1_relset_1(B_165, A_164, C_166)=B_165 | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(B_165, A_164))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.93/1.44  tff(c_539, plain, (r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_4'), '#skF_6'), k1_tarski('#skF_4')) | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_68, c_536])).
% 2.93/1.44  tff(c_551, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_539])).
% 2.93/1.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.44  tff(c_135, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.93/1.44  tff(c_139, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_135])).
% 2.93/1.44  tff(c_32, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.93/1.44  tff(c_146, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_139, c_32])).
% 2.93/1.44  tff(c_148, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_146])).
% 2.93/1.44  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.93/1.44  tff(c_193, plain, (![B_94, A_95]: (k1_tarski(k1_funct_1(B_94, A_95))=k2_relat_1(B_94) | k1_tarski(A_95)!=k1_relat_1(B_94) | ~v1_funct_1(B_94) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.93/1.44  tff(c_182, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.93/1.44  tff(c_186, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_182])).
% 2.93/1.44  tff(c_64, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.93/1.44  tff(c_187, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_64])).
% 2.93/1.44  tff(c_199, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_193, c_187])).
% 2.93/1.44  tff(c_220, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_72, c_199])).
% 2.93/1.44  tff(c_175, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.93/1.44  tff(c_179, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_175])).
% 2.93/1.44  tff(c_28, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.93/1.44  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.44  tff(c_238, plain, (![B_107, C_108, A_109]: (k2_tarski(B_107, C_108)=A_109 | k1_tarski(C_108)=A_109 | k1_tarski(B_107)=A_109 | k1_xboole_0=A_109 | ~r1_tarski(A_109, k2_tarski(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.93/1.44  tff(c_254, plain, (![A_6, A_109]: (k2_tarski(A_6, A_6)=A_109 | k1_tarski(A_6)=A_109 | k1_tarski(A_6)=A_109 | k1_xboole_0=A_109 | ~r1_tarski(A_109, k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_238])).
% 2.93/1.44  tff(c_269, plain, (![A_110, A_111]: (k1_tarski(A_110)=A_111 | k1_tarski(A_110)=A_111 | k1_tarski(A_110)=A_111 | k1_xboole_0=A_111 | ~r1_tarski(A_111, k1_tarski(A_110)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_254])).
% 2.93/1.44  tff(c_293, plain, (![A_112, B_113]: (k1_tarski(A_112)=k1_relat_1(B_113) | k1_relat_1(B_113)=k1_xboole_0 | ~v4_relat_1(B_113, k1_tarski(A_112)) | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_28, c_269])).
% 2.93/1.44  tff(c_299, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_179, c_293])).
% 2.93/1.44  tff(c_302, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_139, c_299])).
% 2.93/1.44  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_220, c_302])).
% 2.93/1.44  tff(c_305, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_146])).
% 2.93/1.44  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.93/1.44  tff(c_310, plain, (![A_5]: (r1_tarski('#skF_6', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_6])).
% 2.93/1.44  tff(c_569, plain, (![D_178, A_179, B_180, C_181]: (r2_hidden(k4_tarski(D_178, '#skF_3'(A_179, B_180, C_181, D_178)), C_181) | ~r2_hidden(D_178, B_180) | k1_relset_1(B_180, A_179, C_181)!=B_180 | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(B_180, A_179))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.93/1.44  tff(c_36, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.93/1.44  tff(c_590, plain, (![C_186, D_187, A_188, B_189]: (~r1_tarski(C_186, k4_tarski(D_187, '#skF_3'(A_188, B_189, C_186, D_187))) | ~r2_hidden(D_187, B_189) | k1_relset_1(B_189, A_188, C_186)!=B_189 | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(B_189, A_188))))), inference(resolution, [status(thm)], [c_569, c_36])).
% 2.93/1.44  tff(c_601, plain, (![D_190, B_191, A_192]: (~r2_hidden(D_190, B_191) | k1_relset_1(B_191, A_192, '#skF_6')!=B_191 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_191, A_192))))), inference(resolution, [status(thm)], [c_310, c_590])).
% 2.93/1.44  tff(c_608, plain, (![A_193, A_194]: (k1_relset_1(A_193, A_194, '#skF_6')!=A_193 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_193, A_194))) | v1_xboole_0(A_193))), inference(resolution, [status(thm)], [c_4, c_601])).
% 2.93/1.44  tff(c_611, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski('#skF_4') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_608])).
% 2.93/1.44  tff(c_614, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_611])).
% 2.93/1.44  tff(c_616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_614])).
% 2.93/1.44  tff(c_618, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_539])).
% 2.93/1.44  tff(c_66, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.93/1.44  tff(c_311, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_305, c_66])).
% 2.93/1.44  tff(c_70, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.93/1.44  tff(c_62, plain, (![B_47, A_46, C_48]: (k1_xboole_0=B_47 | k1_relset_1(A_46, B_47, C_48)=A_46 | ~v1_funct_2(C_48, A_46, B_47) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.93/1.44  tff(c_628, plain, (![B_195, A_196, C_197]: (B_195='#skF_6' | k1_relset_1(A_196, B_195, C_197)=A_196 | ~v1_funct_2(C_197, A_196, B_195) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_62])).
% 2.93/1.44  tff(c_631, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4') | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_68, c_628])).
% 2.93/1.44  tff(c_634, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_631])).
% 2.93/1.44  tff(c_636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_618, c_311, c_634])).
% 2.93/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.44  
% 2.93/1.44  Inference rules
% 2.93/1.44  ----------------------
% 2.93/1.44  #Ref     : 0
% 2.93/1.44  #Sup     : 115
% 2.93/1.44  #Fact    : 0
% 2.93/1.44  #Define  : 0
% 2.93/1.44  #Split   : 4
% 2.93/1.44  #Chain   : 0
% 2.93/1.44  #Close   : 0
% 2.93/1.44  
% 2.93/1.44  Ordering : KBO
% 2.93/1.44  
% 2.93/1.44  Simplification rules
% 2.93/1.44  ----------------------
% 2.93/1.44  #Subsume      : 8
% 2.93/1.44  #Demod        : 70
% 2.93/1.44  #Tautology    : 54
% 2.93/1.44  #SimpNegUnit  : 5
% 2.93/1.44  #BackRed      : 7
% 2.93/1.44  
% 2.93/1.44  #Partial instantiations: 0
% 2.93/1.44  #Strategies tried      : 1
% 2.93/1.44  
% 2.93/1.44  Timing (in seconds)
% 2.93/1.44  ----------------------
% 2.93/1.44  Preprocessing        : 0.34
% 2.93/1.44  Parsing              : 0.18
% 2.93/1.44  CNF conversion       : 0.02
% 2.93/1.44  Main loop            : 0.34
% 2.93/1.44  Inferencing          : 0.13
% 2.93/1.44  Reduction            : 0.11
% 2.93/1.44  Demodulation         : 0.07
% 2.93/1.44  BG Simplification    : 0.02
% 2.93/1.44  Subsumption          : 0.06
% 2.93/1.44  Abstraction          : 0.02
% 2.93/1.44  MUC search           : 0.00
% 2.93/1.44  Cooper               : 0.00
% 2.93/1.44  Total                : 0.72
% 2.93/1.44  Index Insertion      : 0.00
% 2.93/1.44  Index Deletion       : 0.00
% 2.93/1.44  Index Matching       : 0.00
% 2.93/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
