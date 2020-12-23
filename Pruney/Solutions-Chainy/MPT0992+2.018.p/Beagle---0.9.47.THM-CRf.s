%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:33 EST 2020

% Result     : Theorem 10.67s
% Output     : CNFRefutation 10.74s
% Verified   : 
% Statistics : Number of formulae       :  170 (1376 expanded)
%              Number of leaves         :   41 ( 436 expanded)
%              Depth                    :   12
%              Number of atoms          :  273 (4131 expanded)
%              Number of equality atoms :   73 (1354 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_111,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_119,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_111])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_21530,plain,(
    ! [A_851,B_852,C_853] :
      ( k1_relset_1(A_851,B_852,C_853) = k1_relat_1(C_853)
      | ~ m1_subset_1(C_853,k1_zfmisc_1(k2_zfmisc_1(A_851,B_852))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_21542,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_21530])).

tff(c_22109,plain,(
    ! [B_933,A_934,C_935] :
      ( k1_xboole_0 = B_933
      | k1_relset_1(A_934,B_933,C_935) = A_934
      | ~ v1_funct_2(C_935,A_934,B_933)
      | ~ m1_subset_1(C_935,k1_zfmisc_1(k2_zfmisc_1(A_934,B_933))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22118,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_22109])).

tff(c_22129,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_21542,c_22118])).

tff(c_22130,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_22129])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( k1_relat_1(k7_relat_1(B_15,A_14)) = A_14
      | ~ r1_tarski(A_14,k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22152,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_14)) = A_14
      | ~ r1_tarski(A_14,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22130,c_26])).

tff(c_22203,plain,(
    ! [A_936] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_936)) = A_936
      | ~ r1_tarski(A_936,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_22152])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_21993,plain,(
    ! [A_917,B_918,C_919,D_920] :
      ( k2_partfun1(A_917,B_918,C_919,D_920) = k7_relat_1(C_919,D_920)
      | ~ m1_subset_1(C_919,k1_zfmisc_1(k2_zfmisc_1(A_917,B_918)))
      | ~ v1_funct_1(C_919) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_21999,plain,(
    ! [D_920] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_920) = k7_relat_1('#skF_4',D_920)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_21993])).

tff(c_22009,plain,(
    ! [D_920] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_920) = k7_relat_1('#skF_4',D_920) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_21999])).

tff(c_1046,plain,(
    ! [A_193,B_194,C_195,D_196] :
      ( k2_partfun1(A_193,B_194,C_195,D_196) = k7_relat_1(C_195,D_196)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ v1_funct_1(C_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1050,plain,(
    ! [D_196] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_196) = k7_relat_1('#skF_4',D_196)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_1046])).

tff(c_1057,plain,(
    ! [D_196] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_196) = k7_relat_1('#skF_4',D_196) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1050])).

tff(c_1328,plain,(
    ! [A_221,B_222,C_223,D_224] :
      ( m1_subset_1(k2_partfun1(A_221,B_222,C_223,D_224),k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ v1_funct_1(C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1370,plain,(
    ! [D_196] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_196),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1057,c_1328])).

tff(c_1392,plain,(
    ! [D_226] : m1_subset_1(k7_relat_1('#skF_4',D_226),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1370])).

tff(c_28,plain,(
    ! [C_18,A_16,B_17] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1439,plain,(
    ! [D_226] : v1_relat_1(k7_relat_1('#skF_4',D_226)) ),
    inference(resolution,[status(thm)],[c_1392,c_28])).

tff(c_30,plain,(
    ! [C_21,B_20,A_19] :
      ( v5_relat_1(C_21,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1438,plain,(
    ! [D_226] : v5_relat_1(k7_relat_1('#skF_4',D_226),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1392,c_30])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_921,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( v1_funct_1(k2_partfun1(A_173,B_174,C_175,D_176))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1(C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_923,plain,(
    ! [D_176] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_176))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_921])).

tff(c_929,plain,(
    ! [D_176] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_176)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_923])).

tff(c_1070,plain,(
    ! [D_176] : v1_funct_1(k7_relat_1('#skF_4',D_176)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_929])).

tff(c_459,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_467,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_459])).

tff(c_1195,plain,(
    ! [B_215,A_216,C_217] :
      ( k1_xboole_0 = B_215
      | k1_relset_1(A_216,B_215,C_217) = A_216
      | ~ v1_funct_2(C_217,A_216,B_215)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_216,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1201,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1195])).

tff(c_1209,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_467,c_1201])).

tff(c_1210,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1209])).

tff(c_1235,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_14)) = A_14
      | ~ r1_tarski(A_14,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_26])).

tff(c_1488,plain,(
    ! [A_235] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_235)) = A_235
      | ~ r1_tarski(A_235,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_1235])).

tff(c_56,plain,(
    ! [B_41,A_40] :
      ( m1_subset_1(B_41,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_41),A_40)))
      | ~ r1_tarski(k2_relat_1(B_41),A_40)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1506,plain,(
    ! [A_235,A_40] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_235),k1_zfmisc_1(k2_zfmisc_1(A_235,A_40)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_235)),A_40)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_235))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_235))
      | ~ r1_tarski(A_235,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1488,c_56])).

tff(c_21226,plain,(
    ! [A_827,A_828] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_827),k1_zfmisc_1(k2_zfmisc_1(A_827,A_828)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_827)),A_828)
      | ~ r1_tarski(A_827,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1070,c_1506])).

tff(c_336,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( v1_funct_1(k2_partfun1(A_90,B_91,C_92,D_93))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_338,plain,(
    ! [D_93] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_93))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_336])).

tff(c_344,plain,(
    ! [D_93] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_93)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_338])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_134,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_134])).

tff(c_349,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_372,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_1071,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_372])).

tff(c_21256,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_21226,c_1071])).

tff(c_21327,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_21256])).

tff(c_21355,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_21327])).

tff(c_21361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1438,c_21355])).

tff(c_21363,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_21541,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_21363,c_21530])).

tff(c_22022,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22009,c_22009,c_21541])).

tff(c_21362,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_22030,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22009,c_21362])).

tff(c_22029,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22009,c_21363])).

tff(c_44,plain,(
    ! [B_30,C_31,A_29] :
      ( k1_xboole_0 = B_30
      | v1_funct_2(C_31,A_29,B_30)
      | k1_relset_1(A_29,B_30,C_31) != A_29
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22061,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_22029,c_44])).

tff(c_22085,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_22030,c_86,c_22061])).

tff(c_22103,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22022,c_22085])).

tff(c_22212,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22203,c_22103])).

tff(c_22260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_22212])).

tff(c_22261,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_22266,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22261,c_2])).

tff(c_22262,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_22271,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22261,c_22262])).

tff(c_22297,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22271,c_68])).

tff(c_23264,plain,(
    ! [C_1072,A_1073,B_1074] :
      ( v1_xboole_0(C_1072)
      | ~ m1_subset_1(C_1072,k1_zfmisc_1(k2_zfmisc_1(A_1073,B_1074)))
      | ~ v1_xboole_0(A_1073) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_23270,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22297,c_23264])).

tff(c_23280,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22266,c_23270])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_22285,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22261,c_4])).

tff(c_23286,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_23280,c_22285])).

tff(c_22272,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22271,c_70])).

tff(c_23306,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23286,c_23286,c_22272])).

tff(c_22762,plain,(
    ! [C_1009,A_1010,B_1011] :
      ( v1_xboole_0(C_1009)
      | ~ m1_subset_1(C_1009,k1_zfmisc_1(k2_zfmisc_1(A_1010,B_1011)))
      | ~ v1_xboole_0(A_1010) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22765,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22297,c_22762])).

tff(c_22772,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22266,c_22765])).

tff(c_22778,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22772,c_22285])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22264,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22261,c_14])).

tff(c_22788,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22778,c_22264])).

tff(c_24,plain,(
    ! [A_13] : k7_relat_1(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22263,plain,(
    ! [A_13] : k7_relat_1('#skF_1',A_13) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22261,c_22261,c_24])).

tff(c_22790,plain,(
    ! [A_13] : k7_relat_1('#skF_4',A_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22778,c_22778,c_22263])).

tff(c_23145,plain,(
    ! [A_1058,B_1059,C_1060,D_1061] :
      ( k2_partfun1(A_1058,B_1059,C_1060,D_1061) = k7_relat_1(C_1060,D_1061)
      | ~ m1_subset_1(C_1060,k1_zfmisc_1(k2_zfmisc_1(A_1058,B_1059)))
      | ~ v1_funct_1(C_1060) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_23150,plain,(
    ! [A_1058,B_1059,D_1061] :
      ( k2_partfun1(A_1058,B_1059,'#skF_4',D_1061) = k7_relat_1('#skF_4',D_1061)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22788,c_23145])).

tff(c_23154,plain,(
    ! [A_1058,B_1059,D_1061] : k2_partfun1(A_1058,B_1059,'#skF_4',D_1061) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22790,c_23150])).

tff(c_22449,plain,(
    ! [C_965,A_966,B_967] :
      ( v1_xboole_0(C_965)
      | ~ m1_subset_1(C_965,k1_zfmisc_1(k2_zfmisc_1(A_966,B_967)))
      | ~ v1_xboole_0(A_966) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22452,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22297,c_22449])).

tff(c_22459,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22266,c_22452])).

tff(c_22465,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22459,c_22285])).

tff(c_22478,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22465,c_22264])).

tff(c_22717,plain,(
    ! [A_995,B_996,C_997,D_998] :
      ( v1_funct_1(k2_partfun1(A_995,B_996,C_997,D_998))
      | ~ m1_subset_1(C_997,k1_zfmisc_1(k2_zfmisc_1(A_995,B_996)))
      | ~ v1_funct_1(C_997) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_22720,plain,(
    ! [A_995,B_996,D_998] :
      ( v1_funct_1(k2_partfun1(A_995,B_996,'#skF_4',D_998))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22478,c_22717])).

tff(c_22723,plain,(
    ! [A_995,B_996,D_998] : v1_funct_1(k2_partfun1(A_995,B_996,'#skF_4',D_998)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22720])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22265,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22261,c_12])).

tff(c_22310,plain,(
    ! [B_947,A_948] :
      ( B_947 = A_948
      | ~ r1_tarski(B_947,A_948)
      | ~ r1_tarski(A_948,B_947) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22316,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_22310])).

tff(c_22324,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22265,c_22316])).

tff(c_22354,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22324,c_22271,c_22324,c_22324,c_22271,c_22271,c_22324,c_22324,c_22271,c_22271,c_62])).

tff(c_22355,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_22354])).

tff(c_22471,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22465,c_22465,c_22465,c_22355])).

tff(c_22726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22723,c_22471])).

tff(c_22727,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_22354])).

tff(c_22739,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_22727])).

tff(c_22925,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22778,c_22778,c_22778,c_22778,c_22778,c_22739])).

tff(c_23156,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23154,c_22925])).

tff(c_23160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22788,c_23156])).

tff(c_23162,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_22727])).

tff(c_23267,plain,
    ( v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_23162,c_23264])).

tff(c_23277,plain,(
    v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22266,c_23267])).

tff(c_23439,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23286,c_23286,c_23286,c_23277])).

tff(c_23304,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23286,c_22285])).

tff(c_23443,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_23439,c_23304])).

tff(c_23161,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_22727])).

tff(c_23295,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23286,c_23286,c_23286,c_23286,c_23286,c_23161])).

tff(c_23510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23306,c_23443,c_23295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:06:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.67/4.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.74/4.31  
% 10.74/4.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.74/4.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.74/4.32  
% 10.74/4.32  %Foreground sorts:
% 10.74/4.32  
% 10.74/4.32  
% 10.74/4.32  %Background operators:
% 10.74/4.32  
% 10.74/4.32  
% 10.74/4.32  %Foreground operators:
% 10.74/4.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.74/4.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.74/4.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.74/4.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.74/4.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.74/4.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.74/4.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.74/4.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.74/4.32  tff('#skF_2', type, '#skF_2': $i).
% 10.74/4.32  tff('#skF_3', type, '#skF_3': $i).
% 10.74/4.32  tff('#skF_1', type, '#skF_1': $i).
% 10.74/4.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.74/4.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.74/4.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.74/4.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.74/4.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.74/4.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.74/4.32  tff('#skF_4', type, '#skF_4': $i).
% 10.74/4.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.74/4.32  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.74/4.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.74/4.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.74/4.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.74/4.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.74/4.32  
% 10.74/4.34  tff(f_149, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 10.74/4.34  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.74/4.34  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.74/4.34  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.74/4.34  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 10.74/4.34  tff(f_117, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 10.74/4.34  tff(f_111, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 10.74/4.34  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.74/4.34  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 10.74/4.34  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 10.74/4.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.74/4.34  tff(f_81, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 10.74/4.34  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.74/4.34  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.74/4.34  tff(f_58, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 10.74/4.34  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.74/4.34  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.74/4.34  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.74/4.34  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.74/4.34  tff(c_111, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.74/4.34  tff(c_119, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_111])).
% 10.74/4.34  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.74/4.34  tff(c_86, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 10.74/4.34  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.74/4.34  tff(c_21530, plain, (![A_851, B_852, C_853]: (k1_relset_1(A_851, B_852, C_853)=k1_relat_1(C_853) | ~m1_subset_1(C_853, k1_zfmisc_1(k2_zfmisc_1(A_851, B_852))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.74/4.34  tff(c_21542, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_21530])).
% 10.74/4.34  tff(c_22109, plain, (![B_933, A_934, C_935]: (k1_xboole_0=B_933 | k1_relset_1(A_934, B_933, C_935)=A_934 | ~v1_funct_2(C_935, A_934, B_933) | ~m1_subset_1(C_935, k1_zfmisc_1(k2_zfmisc_1(A_934, B_933))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.74/4.34  tff(c_22118, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_22109])).
% 10.74/4.34  tff(c_22129, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_21542, c_22118])).
% 10.74/4.34  tff(c_22130, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_22129])).
% 10.74/4.34  tff(c_26, plain, (![B_15, A_14]: (k1_relat_1(k7_relat_1(B_15, A_14))=A_14 | ~r1_tarski(A_14, k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.74/4.34  tff(c_22152, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_4', A_14))=A_14 | ~r1_tarski(A_14, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_22130, c_26])).
% 10.74/4.34  tff(c_22203, plain, (![A_936]: (k1_relat_1(k7_relat_1('#skF_4', A_936))=A_936 | ~r1_tarski(A_936, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_22152])).
% 10.74/4.34  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.74/4.34  tff(c_21993, plain, (![A_917, B_918, C_919, D_920]: (k2_partfun1(A_917, B_918, C_919, D_920)=k7_relat_1(C_919, D_920) | ~m1_subset_1(C_919, k1_zfmisc_1(k2_zfmisc_1(A_917, B_918))) | ~v1_funct_1(C_919))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.74/4.34  tff(c_21999, plain, (![D_920]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_920)=k7_relat_1('#skF_4', D_920) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_21993])).
% 10.74/4.34  tff(c_22009, plain, (![D_920]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_920)=k7_relat_1('#skF_4', D_920))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_21999])).
% 10.74/4.34  tff(c_1046, plain, (![A_193, B_194, C_195, D_196]: (k2_partfun1(A_193, B_194, C_195, D_196)=k7_relat_1(C_195, D_196) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~v1_funct_1(C_195))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.74/4.34  tff(c_1050, plain, (![D_196]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_196)=k7_relat_1('#skF_4', D_196) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_1046])).
% 10.74/4.34  tff(c_1057, plain, (![D_196]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_196)=k7_relat_1('#skF_4', D_196))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1050])).
% 10.74/4.34  tff(c_1328, plain, (![A_221, B_222, C_223, D_224]: (m1_subset_1(k2_partfun1(A_221, B_222, C_223, D_224), k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~v1_funct_1(C_223))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.74/4.34  tff(c_1370, plain, (![D_196]: (m1_subset_1(k7_relat_1('#skF_4', D_196), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1057, c_1328])).
% 10.74/4.34  tff(c_1392, plain, (![D_226]: (m1_subset_1(k7_relat_1('#skF_4', D_226), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1370])).
% 10.74/4.34  tff(c_28, plain, (![C_18, A_16, B_17]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.74/4.34  tff(c_1439, plain, (![D_226]: (v1_relat_1(k7_relat_1('#skF_4', D_226)))), inference(resolution, [status(thm)], [c_1392, c_28])).
% 10.74/4.34  tff(c_30, plain, (![C_21, B_20, A_19]: (v5_relat_1(C_21, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.74/4.34  tff(c_1438, plain, (![D_226]: (v5_relat_1(k7_relat_1('#skF_4', D_226), '#skF_2'))), inference(resolution, [status(thm)], [c_1392, c_30])).
% 10.74/4.34  tff(c_20, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.74/4.34  tff(c_921, plain, (![A_173, B_174, C_175, D_176]: (v1_funct_1(k2_partfun1(A_173, B_174, C_175, D_176)) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1(C_175))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.74/4.34  tff(c_923, plain, (![D_176]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_176)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_921])).
% 10.74/4.34  tff(c_929, plain, (![D_176]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_176)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_923])).
% 10.74/4.34  tff(c_1070, plain, (![D_176]: (v1_funct_1(k7_relat_1('#skF_4', D_176)))), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_929])).
% 10.74/4.34  tff(c_459, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.74/4.34  tff(c_467, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_459])).
% 10.74/4.34  tff(c_1195, plain, (![B_215, A_216, C_217]: (k1_xboole_0=B_215 | k1_relset_1(A_216, B_215, C_217)=A_216 | ~v1_funct_2(C_217, A_216, B_215) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_216, B_215))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.74/4.34  tff(c_1201, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_1195])).
% 10.74/4.34  tff(c_1209, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_467, c_1201])).
% 10.74/4.34  tff(c_1210, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_1209])).
% 10.74/4.34  tff(c_1235, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_4', A_14))=A_14 | ~r1_tarski(A_14, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1210, c_26])).
% 10.74/4.34  tff(c_1488, plain, (![A_235]: (k1_relat_1(k7_relat_1('#skF_4', A_235))=A_235 | ~r1_tarski(A_235, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_1235])).
% 10.74/4.34  tff(c_56, plain, (![B_41, A_40]: (m1_subset_1(B_41, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_41), A_40))) | ~r1_tarski(k2_relat_1(B_41), A_40) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.74/4.34  tff(c_1506, plain, (![A_235, A_40]: (m1_subset_1(k7_relat_1('#skF_4', A_235), k1_zfmisc_1(k2_zfmisc_1(A_235, A_40))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_235)), A_40) | ~v1_funct_1(k7_relat_1('#skF_4', A_235)) | ~v1_relat_1(k7_relat_1('#skF_4', A_235)) | ~r1_tarski(A_235, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1488, c_56])).
% 10.74/4.34  tff(c_21226, plain, (![A_827, A_828]: (m1_subset_1(k7_relat_1('#skF_4', A_827), k1_zfmisc_1(k2_zfmisc_1(A_827, A_828))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_827)), A_828) | ~r1_tarski(A_827, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1070, c_1506])).
% 10.74/4.34  tff(c_336, plain, (![A_90, B_91, C_92, D_93]: (v1_funct_1(k2_partfun1(A_90, B_91, C_92, D_93)) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.74/4.34  tff(c_338, plain, (![D_93]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_93)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_336])).
% 10.74/4.34  tff(c_344, plain, (![D_93]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_93)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_338])).
% 10.74/4.34  tff(c_62, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.74/4.34  tff(c_134, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 10.74/4.34  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_134])).
% 10.74/4.34  tff(c_349, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 10.74/4.34  tff(c_372, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_349])).
% 10.74/4.34  tff(c_1071, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_372])).
% 10.74/4.34  tff(c_21256, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_21226, c_1071])).
% 10.74/4.34  tff(c_21327, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_21256])).
% 10.74/4.34  tff(c_21355, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_21327])).
% 10.74/4.34  tff(c_21361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1438, c_21355])).
% 10.74/4.34  tff(c_21363, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_349])).
% 10.74/4.34  tff(c_21541, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_21363, c_21530])).
% 10.74/4.34  tff(c_22022, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22009, c_22009, c_21541])).
% 10.74/4.34  tff(c_21362, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_349])).
% 10.74/4.34  tff(c_22030, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22009, c_21362])).
% 10.74/4.34  tff(c_22029, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22009, c_21363])).
% 10.74/4.34  tff(c_44, plain, (![B_30, C_31, A_29]: (k1_xboole_0=B_30 | v1_funct_2(C_31, A_29, B_30) | k1_relset_1(A_29, B_30, C_31)!=A_29 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.74/4.34  tff(c_22061, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_22029, c_44])).
% 10.74/4.34  tff(c_22085, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_22030, c_86, c_22061])).
% 10.74/4.34  tff(c_22103, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22022, c_22085])).
% 10.74/4.34  tff(c_22212, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22203, c_22103])).
% 10.74/4.34  tff(c_22260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_22212])).
% 10.74/4.34  tff(c_22261, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 10.74/4.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.74/4.34  tff(c_22266, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22261, c_2])).
% 10.74/4.34  tff(c_22262, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 10.74/4.34  tff(c_22271, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22261, c_22262])).
% 10.74/4.34  tff(c_22297, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22271, c_68])).
% 10.74/4.34  tff(c_23264, plain, (![C_1072, A_1073, B_1074]: (v1_xboole_0(C_1072) | ~m1_subset_1(C_1072, k1_zfmisc_1(k2_zfmisc_1(A_1073, B_1074))) | ~v1_xboole_0(A_1073))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.74/4.34  tff(c_23270, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22297, c_23264])).
% 10.74/4.34  tff(c_23280, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22266, c_23270])).
% 10.74/4.34  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 10.74/4.34  tff(c_22285, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_22261, c_4])).
% 10.74/4.34  tff(c_23286, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_23280, c_22285])).
% 10.74/4.34  tff(c_22272, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22271, c_70])).
% 10.74/4.34  tff(c_23306, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23286, c_23286, c_22272])).
% 10.74/4.34  tff(c_22762, plain, (![C_1009, A_1010, B_1011]: (v1_xboole_0(C_1009) | ~m1_subset_1(C_1009, k1_zfmisc_1(k2_zfmisc_1(A_1010, B_1011))) | ~v1_xboole_0(A_1010))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.74/4.34  tff(c_22765, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22297, c_22762])).
% 10.74/4.34  tff(c_22772, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22266, c_22765])).
% 10.74/4.34  tff(c_22778, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_22772, c_22285])).
% 10.74/4.34  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.74/4.34  tff(c_22264, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_22261, c_14])).
% 10.74/4.34  tff(c_22788, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_22778, c_22264])).
% 10.74/4.34  tff(c_24, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.74/4.34  tff(c_22263, plain, (![A_13]: (k7_relat_1('#skF_1', A_13)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22261, c_22261, c_24])).
% 10.74/4.34  tff(c_22790, plain, (![A_13]: (k7_relat_1('#skF_4', A_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22778, c_22778, c_22263])).
% 10.74/4.34  tff(c_23145, plain, (![A_1058, B_1059, C_1060, D_1061]: (k2_partfun1(A_1058, B_1059, C_1060, D_1061)=k7_relat_1(C_1060, D_1061) | ~m1_subset_1(C_1060, k1_zfmisc_1(k2_zfmisc_1(A_1058, B_1059))) | ~v1_funct_1(C_1060))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.74/4.34  tff(c_23150, plain, (![A_1058, B_1059, D_1061]: (k2_partfun1(A_1058, B_1059, '#skF_4', D_1061)=k7_relat_1('#skF_4', D_1061) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22788, c_23145])).
% 10.74/4.34  tff(c_23154, plain, (![A_1058, B_1059, D_1061]: (k2_partfun1(A_1058, B_1059, '#skF_4', D_1061)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_22790, c_23150])).
% 10.74/4.34  tff(c_22449, plain, (![C_965, A_966, B_967]: (v1_xboole_0(C_965) | ~m1_subset_1(C_965, k1_zfmisc_1(k2_zfmisc_1(A_966, B_967))) | ~v1_xboole_0(A_966))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.74/4.34  tff(c_22452, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22297, c_22449])).
% 10.74/4.34  tff(c_22459, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22266, c_22452])).
% 10.74/4.34  tff(c_22465, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_22459, c_22285])).
% 10.74/4.34  tff(c_22478, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_22465, c_22264])).
% 10.74/4.34  tff(c_22717, plain, (![A_995, B_996, C_997, D_998]: (v1_funct_1(k2_partfun1(A_995, B_996, C_997, D_998)) | ~m1_subset_1(C_997, k1_zfmisc_1(k2_zfmisc_1(A_995, B_996))) | ~v1_funct_1(C_997))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.74/4.34  tff(c_22720, plain, (![A_995, B_996, D_998]: (v1_funct_1(k2_partfun1(A_995, B_996, '#skF_4', D_998)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22478, c_22717])).
% 10.74/4.34  tff(c_22723, plain, (![A_995, B_996, D_998]: (v1_funct_1(k2_partfun1(A_995, B_996, '#skF_4', D_998)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_22720])).
% 10.74/4.34  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.74/4.34  tff(c_22265, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_22261, c_12])).
% 10.74/4.34  tff(c_22310, plain, (![B_947, A_948]: (B_947=A_948 | ~r1_tarski(B_947, A_948) | ~r1_tarski(A_948, B_947))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.74/4.34  tff(c_22316, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_22310])).
% 10.74/4.34  tff(c_22324, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22265, c_22316])).
% 10.74/4.34  tff(c_22354, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22324, c_22271, c_22324, c_22324, c_22271, c_22271, c_22324, c_22324, c_22271, c_22271, c_62])).
% 10.74/4.34  tff(c_22355, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_22354])).
% 10.74/4.34  tff(c_22471, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22465, c_22465, c_22465, c_22355])).
% 10.74/4.34  tff(c_22726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22723, c_22471])).
% 10.74/4.34  tff(c_22727, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_22354])).
% 10.74/4.34  tff(c_22739, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_22727])).
% 10.74/4.34  tff(c_22925, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_22778, c_22778, c_22778, c_22778, c_22778, c_22739])).
% 10.74/4.34  tff(c_23156, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_23154, c_22925])).
% 10.74/4.34  tff(c_23160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22788, c_23156])).
% 10.74/4.34  tff(c_23162, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_22727])).
% 10.74/4.34  tff(c_23267, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_23162, c_23264])).
% 10.74/4.34  tff(c_23277, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22266, c_23267])).
% 10.74/4.34  tff(c_23439, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_23286, c_23286, c_23286, c_23277])).
% 10.74/4.34  tff(c_23304, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_23286, c_22285])).
% 10.74/4.34  tff(c_23443, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_23439, c_23304])).
% 10.74/4.34  tff(c_23161, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_22727])).
% 10.74/4.34  tff(c_23295, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23286, c_23286, c_23286, c_23286, c_23286, c_23161])).
% 10.74/4.34  tff(c_23510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23306, c_23443, c_23295])).
% 10.74/4.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.74/4.34  
% 10.74/4.34  Inference rules
% 10.74/4.34  ----------------------
% 10.74/4.34  #Ref     : 0
% 10.74/4.34  #Sup     : 4799
% 10.74/4.34  #Fact    : 0
% 10.74/4.34  #Define  : 0
% 10.74/4.34  #Split   : 22
% 10.74/4.34  #Chain   : 0
% 10.74/4.34  #Close   : 0
% 10.74/4.34  
% 10.74/4.34  Ordering : KBO
% 10.74/4.34  
% 10.74/4.34  Simplification rules
% 10.74/4.34  ----------------------
% 10.74/4.34  #Subsume      : 1114
% 10.74/4.34  #Demod        : 10388
% 10.74/4.34  #Tautology    : 2226
% 10.74/4.34  #SimpNegUnit  : 150
% 10.74/4.34  #BackRed      : 130
% 10.74/4.34  
% 10.74/4.34  #Partial instantiations: 0
% 10.74/4.34  #Strategies tried      : 1
% 10.74/4.34  
% 10.74/4.34  Timing (in seconds)
% 10.74/4.34  ----------------------
% 10.74/4.34  Preprocessing        : 0.36
% 10.74/4.34  Parsing              : 0.19
% 10.74/4.34  CNF conversion       : 0.02
% 10.74/4.34  Main loop            : 3.20
% 10.74/4.34  Inferencing          : 0.84
% 10.74/4.34  Reduction            : 1.43
% 10.74/4.34  Demodulation         : 1.15
% 10.74/4.34  BG Simplification    : 0.09
% 10.74/4.34  Subsumption          : 0.67
% 10.74/4.34  Abstraction          : 0.11
% 10.74/4.34  MUC search           : 0.00
% 10.74/4.34  Cooper               : 0.00
% 10.74/4.34  Total                : 3.62
% 10.74/4.34  Index Insertion      : 0.00
% 10.74/4.34  Index Deletion       : 0.00
% 10.74/4.34  Index Matching       : 0.00
% 10.74/4.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
