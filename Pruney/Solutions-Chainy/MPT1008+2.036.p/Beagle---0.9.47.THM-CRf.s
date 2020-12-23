%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:31 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 159 expanded)
%              Number of leaves         :   47 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  136 ( 297 expanded)
%              Number of equality atoms :   57 ( 122 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_127,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_80,plain,(
    ! [A_57] : k2_tarski(A_57,A_57) = k1_tarski(A_57) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_12,B_13] : ~ v1_xboole_0(k2_tarski(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_57] : ~ v1_xboole_0(k1_tarski(A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_14])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_121,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_129,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_121])).

tff(c_32,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_137,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_129,c_32])).

tff(c_149,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( k1_tarski(k1_funct_1(B_24,A_23)) = k2_relat_1(B_24)
      | k1_tarski(A_23) != k1_relat_1(B_24)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_232,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_relset_1(A_97,B_98,C_99) = k2_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_240,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_232])).

tff(c_64,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_249,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_64])).

tff(c_276,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_249])).

tff(c_279,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_72,c_276])).

tff(c_183,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_191,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_183])).

tff(c_163,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(k1_relat_1(B_75),A_76)
      | ~ v4_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k1_tarski(B_15) = A_14
      | k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_tarski(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_288,plain,(
    ! [B_108,B_109] :
      ( k1_tarski(B_108) = k1_relat_1(B_109)
      | k1_relat_1(B_109) = k1_xboole_0
      | ~ v4_relat_1(B_109,k1_tarski(B_108))
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_163,c_16])).

tff(c_294,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_191,c_288])).

tff(c_301,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_294])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_279,c_301])).

tff(c_304,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_313,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_66])).

tff(c_70,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_311,plain,(
    ! [A_16] : m1_subset_1('#skF_6',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_22])).

tff(c_62,plain,(
    ! [B_50,A_49,C_51] :
      ( k1_xboole_0 = B_50
      | k1_relset_1(A_49,B_50,C_51) = A_49
      | ~ v1_funct_2(C_51,A_49,B_50)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_564,plain,(
    ! [B_167,A_168,C_169] :
      ( B_167 = '#skF_6'
      | k1_relset_1(A_168,B_167,C_169) = A_168
      | ~ v1_funct_2(C_169,A_168,B_167)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_62])).

tff(c_571,plain,(
    ! [B_171,A_172] :
      ( B_171 = '#skF_6'
      | k1_relset_1(A_172,B_171,'#skF_6') = A_172
      | ~ v1_funct_2('#skF_6',A_172,B_171) ) ),
    inference(resolution,[status(thm)],[c_311,c_564])).

tff(c_580,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_571])).

tff(c_587,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_580])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_312,plain,(
    ! [A_5] : r1_tarski('#skF_6',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_6])).

tff(c_655,plain,(
    ! [D_193,A_194,B_195,C_196] :
      ( r2_hidden(k4_tarski(D_193,'#skF_3'(A_194,B_195,C_196,D_193)),C_196)
      | ~ r2_hidden(D_193,B_195)
      | k1_relset_1(B_195,A_194,C_196) != B_195
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(B_195,A_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_36,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_685,plain,(
    ! [C_201,D_202,A_203,B_204] :
      ( ~ r1_tarski(C_201,k4_tarski(D_202,'#skF_3'(A_203,B_204,C_201,D_202)))
      | ~ r2_hidden(D_202,B_204)
      | k1_relset_1(B_204,A_203,C_201) != B_204
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(B_204,A_203))) ) ),
    inference(resolution,[status(thm)],[c_655,c_36])).

tff(c_693,plain,(
    ! [D_202,B_204,A_203] :
      ( ~ r2_hidden(D_202,B_204)
      | k1_relset_1(B_204,A_203,'#skF_6') != B_204
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_204,A_203))) ) ),
    inference(resolution,[status(thm)],[c_312,c_685])).

tff(c_698,plain,(
    ! [D_205,B_206,A_207] :
      ( ~ r2_hidden(D_205,B_206)
      | k1_relset_1(B_206,A_207,'#skF_6') != B_206 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_693])).

tff(c_708,plain,(
    ! [A_208,A_209] :
      ( k1_relset_1(A_208,A_209,'#skF_6') != A_208
      | v1_xboole_0(A_208) ) ),
    inference(resolution,[status(thm)],[c_4,c_698])).

tff(c_710,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_708])).

tff(c_716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:01:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.44  
% 2.82/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.82/1.44  
% 2.82/1.44  %Foreground sorts:
% 2.82/1.44  
% 2.82/1.44  
% 2.82/1.44  %Background operators:
% 2.82/1.44  
% 2.82/1.44  
% 2.82/1.44  %Foreground operators:
% 2.82/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.82/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.82/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.82/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.82/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.82/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.82/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.82/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.82/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.82/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.82/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.82/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.82/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.82/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.44  
% 3.09/1.45  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.09/1.45  tff(f_42, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 3.09/1.45  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.09/1.45  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.09/1.45  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.09/1.45  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.09/1.45  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.09/1.45  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.09/1.45  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.09/1.45  tff(f_48, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.09/1.45  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.09/1.45  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.09/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.09/1.45  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.09/1.45  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 3.09/1.45  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.09/1.45  tff(c_80, plain, (![A_57]: (k2_tarski(A_57, A_57)=k1_tarski(A_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.45  tff(c_14, plain, (![A_12, B_13]: (~v1_xboole_0(k2_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.09/1.45  tff(c_85, plain, (![A_57]: (~v1_xboole_0(k1_tarski(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_14])).
% 3.09/1.45  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.09/1.45  tff(c_121, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.09/1.45  tff(c_129, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_121])).
% 3.09/1.45  tff(c_32, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.09/1.45  tff(c_137, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_129, c_32])).
% 3.09/1.45  tff(c_149, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_137])).
% 3.09/1.45  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.09/1.45  tff(c_34, plain, (![B_24, A_23]: (k1_tarski(k1_funct_1(B_24, A_23))=k2_relat_1(B_24) | k1_tarski(A_23)!=k1_relat_1(B_24) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.45  tff(c_232, plain, (![A_97, B_98, C_99]: (k2_relset_1(A_97, B_98, C_99)=k2_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.09/1.45  tff(c_240, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_232])).
% 3.09/1.45  tff(c_64, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.09/1.45  tff(c_249, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_64])).
% 3.09/1.45  tff(c_276, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_34, c_249])).
% 3.09/1.45  tff(c_279, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_72, c_276])).
% 3.09/1.45  tff(c_183, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.09/1.45  tff(c_191, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_183])).
% 3.09/1.45  tff(c_163, plain, (![B_75, A_76]: (r1_tarski(k1_relat_1(B_75), A_76) | ~v4_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.09/1.45  tff(c_16, plain, (![B_15, A_14]: (k1_tarski(B_15)=A_14 | k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_tarski(B_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.09/1.45  tff(c_288, plain, (![B_108, B_109]: (k1_tarski(B_108)=k1_relat_1(B_109) | k1_relat_1(B_109)=k1_xboole_0 | ~v4_relat_1(B_109, k1_tarski(B_108)) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_163, c_16])).
% 3.09/1.45  tff(c_294, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_191, c_288])).
% 3.09/1.45  tff(c_301, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_129, c_294])).
% 3.09/1.45  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_279, c_301])).
% 3.09/1.45  tff(c_304, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_137])).
% 3.09/1.45  tff(c_66, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.09/1.45  tff(c_313, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_304, c_66])).
% 3.09/1.45  tff(c_70, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.09/1.45  tff(c_22, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.09/1.45  tff(c_311, plain, (![A_16]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_22])).
% 3.09/1.45  tff(c_62, plain, (![B_50, A_49, C_51]: (k1_xboole_0=B_50 | k1_relset_1(A_49, B_50, C_51)=A_49 | ~v1_funct_2(C_51, A_49, B_50) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.09/1.45  tff(c_564, plain, (![B_167, A_168, C_169]: (B_167='#skF_6' | k1_relset_1(A_168, B_167, C_169)=A_168 | ~v1_funct_2(C_169, A_168, B_167) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_62])).
% 3.09/1.45  tff(c_571, plain, (![B_171, A_172]: (B_171='#skF_6' | k1_relset_1(A_172, B_171, '#skF_6')=A_172 | ~v1_funct_2('#skF_6', A_172, B_171))), inference(resolution, [status(thm)], [c_311, c_564])).
% 3.09/1.45  tff(c_580, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_70, c_571])).
% 3.09/1.45  tff(c_587, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_313, c_580])).
% 3.09/1.45  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.45  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.09/1.45  tff(c_312, plain, (![A_5]: (r1_tarski('#skF_6', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_6])).
% 3.09/1.45  tff(c_655, plain, (![D_193, A_194, B_195, C_196]: (r2_hidden(k4_tarski(D_193, '#skF_3'(A_194, B_195, C_196, D_193)), C_196) | ~r2_hidden(D_193, B_195) | k1_relset_1(B_195, A_194, C_196)!=B_195 | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(B_195, A_194))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.09/1.45  tff(c_36, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.09/1.45  tff(c_685, plain, (![C_201, D_202, A_203, B_204]: (~r1_tarski(C_201, k4_tarski(D_202, '#skF_3'(A_203, B_204, C_201, D_202))) | ~r2_hidden(D_202, B_204) | k1_relset_1(B_204, A_203, C_201)!=B_204 | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(B_204, A_203))))), inference(resolution, [status(thm)], [c_655, c_36])).
% 3.09/1.45  tff(c_693, plain, (![D_202, B_204, A_203]: (~r2_hidden(D_202, B_204) | k1_relset_1(B_204, A_203, '#skF_6')!=B_204 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_204, A_203))))), inference(resolution, [status(thm)], [c_312, c_685])).
% 3.09/1.45  tff(c_698, plain, (![D_205, B_206, A_207]: (~r2_hidden(D_205, B_206) | k1_relset_1(B_206, A_207, '#skF_6')!=B_206)), inference(demodulation, [status(thm), theory('equality')], [c_311, c_693])).
% 3.09/1.45  tff(c_708, plain, (![A_208, A_209]: (k1_relset_1(A_208, A_209, '#skF_6')!=A_208 | v1_xboole_0(A_208))), inference(resolution, [status(thm)], [c_4, c_698])).
% 3.09/1.45  tff(c_710, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_587, c_708])).
% 3.09/1.45  tff(c_716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_710])).
% 3.09/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.45  
% 3.09/1.45  Inference rules
% 3.09/1.45  ----------------------
% 3.09/1.45  #Ref     : 0
% 3.09/1.45  #Sup     : 126
% 3.09/1.45  #Fact    : 0
% 3.09/1.45  #Define  : 0
% 3.09/1.45  #Split   : 2
% 3.09/1.45  #Chain   : 0
% 3.09/1.45  #Close   : 0
% 3.09/1.45  
% 3.09/1.45  Ordering : KBO
% 3.09/1.45  
% 3.09/1.45  Simplification rules
% 3.09/1.45  ----------------------
% 3.09/1.45  #Subsume      : 2
% 3.09/1.45  #Demod        : 79
% 3.09/1.45  #Tautology    : 63
% 3.09/1.45  #SimpNegUnit  : 3
% 3.09/1.45  #BackRed      : 11
% 3.09/1.45  
% 3.09/1.45  #Partial instantiations: 0
% 3.09/1.45  #Strategies tried      : 1
% 3.09/1.46  
% 3.09/1.46  Timing (in seconds)
% 3.09/1.46  ----------------------
% 3.09/1.46  Preprocessing        : 0.34
% 3.09/1.46  Parsing              : 0.18
% 3.09/1.46  CNF conversion       : 0.02
% 3.09/1.46  Main loop            : 0.34
% 3.09/1.46  Inferencing          : 0.12
% 3.09/1.46  Reduction            : 0.10
% 3.09/1.46  Demodulation         : 0.07
% 3.09/1.46  BG Simplification    : 0.02
% 3.09/1.46  Subsumption          : 0.06
% 3.09/1.46  Abstraction          : 0.02
% 3.13/1.46  MUC search           : 0.00
% 3.13/1.46  Cooper               : 0.00
% 3.13/1.46  Total                : 0.71
% 3.13/1.46  Index Insertion      : 0.00
% 3.13/1.46  Index Deletion       : 0.00
% 3.13/1.46  Index Matching       : 0.00
% 3.13/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
