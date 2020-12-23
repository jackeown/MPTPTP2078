%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:54 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  137 (1711 expanded)
%              Number of leaves         :   32 ( 513 expanded)
%              Depth                    :   18
%              Number of atoms          :  277 (6673 expanded)
%              Number of equality atoms :   65 (2495 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
             => ( ( C = k1_xboole_0
                  & B != k1_xboole_0 )
                | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(c_30,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_48])).

tff(c_67,plain,(
    ! [C_33,B_34,A_35] :
      ( v5_relat_1(C_33,B_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_74,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_190,plain,(
    ! [D_66,B_67,C_63,F_65,A_62,E_64] :
      ( k1_partfun1(A_62,B_67,C_63,D_66,E_64,F_65) = k5_relat_1(E_64,F_65)
      | ~ m1_subset_1(F_65,k1_zfmisc_1(k2_zfmisc_1(C_63,D_66)))
      | ~ v1_funct_1(F_65)
      | ~ m1_subset_1(E_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_67)))
      | ~ v1_funct_1(E_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_194,plain,(
    ! [A_62,B_67,E_64] :
      ( k1_partfun1(A_62,B_67,'#skF_2','#skF_3',E_64,'#skF_5') = k5_relat_1(E_64,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_67)))
      | ~ v1_funct_1(E_64) ) ),
    inference(resolution,[status(thm)],[c_36,c_190])).

tff(c_222,plain,(
    ! [A_71,B_72,E_73] :
      ( k1_partfun1(A_71,B_72,'#skF_2','#skF_3',E_73,'#skF_5') = k5_relat_1(E_73,'#skF_5')
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_1(E_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_194])).

tff(c_225,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_222])).

tff(c_231,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_225])).

tff(c_34,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_235,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_34])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_47,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_81,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_relset_1(A_38,B_39,C_40) = k1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_89,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_81])).

tff(c_102,plain,(
    ! [B_48,A_49,C_50] :
      ( k1_xboole_0 = B_48
      | k1_relset_1(A_49,B_48,C_50) = A_49
      | ~ v1_funct_2(C_50,A_49,B_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_108,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_102])).

tff(c_114,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_89,c_108])).

tff(c_115,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_114])).

tff(c_149,plain,(
    ! [B_54,A_55] :
      ( v2_funct_1(B_54)
      | ~ r1_tarski(k2_relat_1(B_54),k1_relat_1(A_55))
      | ~ v2_funct_1(k5_relat_1(B_54,A_55))
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_155,plain,(
    ! [B_54] :
      ( v2_funct_1(B_54)
      | ~ r1_tarski(k2_relat_1(B_54),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_54,'#skF_5'))
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_149])).

tff(c_172,plain,(
    ! [B_58] :
      ( v2_funct_1(B_58)
      | ~ r1_tarski(k2_relat_1(B_58),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_58,'#skF_5'))
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_40,c_155])).

tff(c_177,plain,(
    ! [B_2] :
      ( v2_funct_1(B_2)
      | ~ v2_funct_1(k5_relat_1(B_2,'#skF_5'))
      | ~ v1_funct_1(B_2)
      | ~ v5_relat_1(B_2,'#skF_2')
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_172])).

tff(c_242,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_235,c_177])).

tff(c_245,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_74,c_46,c_242])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_245])).

tff(c_249,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_248,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_254,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_248])).

tff(c_266,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_42])).

tff(c_267,plain,(
    ! [C_74,A_75,B_76] :
      ( v1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_274,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_266,c_267])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_259,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_44])).

tff(c_18,plain,(
    ! [C_17,A_15] :
      ( k1_xboole_0 = C_17
      | ~ v1_funct_2(C_17,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_321,plain,(
    ! [C_91,A_92] :
      ( C_91 = '#skF_3'
      | ~ v1_funct_2(C_91,A_92,'#skF_3')
      | A_92 = '#skF_3'
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_249,c_249,c_249,c_18])).

tff(c_324,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_266,c_321])).

tff(c_330,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_324])).

tff(c_335,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_292,plain,(
    ! [C_84,B_85,A_86] :
      ( v5_relat_1(C_84,B_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_299,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_266,c_292])).

tff(c_341,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_299])).

tff(c_344,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_266])).

tff(c_265,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_36])).

tff(c_345,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_335,c_265])).

tff(c_542,plain,(
    ! [A_116,B_121,D_120,C_117,F_119,E_118] :
      ( k1_partfun1(A_116,B_121,C_117,D_120,E_118,F_119) = k5_relat_1(E_118,F_119)
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_117,D_120)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_121)))
      | ~ v1_funct_1(E_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_546,plain,(
    ! [A_116,B_121,E_118] :
      ( k1_partfun1(A_116,B_121,'#skF_1','#skF_1',E_118,'#skF_5') = k5_relat_1(E_118,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_121)))
      | ~ v1_funct_1(E_118) ) ),
    inference(resolution,[status(thm)],[c_345,c_542])).

tff(c_574,plain,(
    ! [A_125,B_126,E_127] :
      ( k1_partfun1(A_125,B_126,'#skF_1','#skF_1',E_127,'#skF_5') = k5_relat_1(E_127,'#skF_5')
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_1(E_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_546])).

tff(c_577,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_344,c_574])).

tff(c_583,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_577])).

tff(c_276,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_254,c_34])).

tff(c_343,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_335,c_335,c_276])).

tff(c_587,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_343])).

tff(c_275,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_265,c_267])).

tff(c_264,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_38])).

tff(c_347,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_335,c_264])).

tff(c_349,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_249])).

tff(c_24,plain,(
    ! [B_16,C_17] :
      ( k1_relset_1(k1_xboole_0,B_16,C_17) = k1_xboole_0
      | ~ v1_funct_2(C_17,k1_xboole_0,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_388,plain,(
    ! [B_95,C_96] :
      ( k1_relset_1('#skF_1',B_95,C_96) = '#skF_1'
      | ~ v1_funct_2(C_96,'#skF_1',B_95)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_95))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_349,c_349,c_349,c_24])).

tff(c_391,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_345,c_388])).

tff(c_394,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_391])).

tff(c_301,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_309,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_265,c_301])).

tff(c_338,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_335,c_309])).

tff(c_399,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_338])).

tff(c_501,plain,(
    ! [B_108,A_109] :
      ( v2_funct_1(B_108)
      | ~ r1_tarski(k2_relat_1(B_108),k1_relat_1(A_109))
      | ~ v2_funct_1(k5_relat_1(B_108,A_109))
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108)
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_507,plain,(
    ! [B_108] :
      ( v2_funct_1(B_108)
      | ~ r1_tarski(k2_relat_1(B_108),'#skF_1')
      | ~ v2_funct_1(k5_relat_1(B_108,'#skF_5'))
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_501])).

tff(c_524,plain,(
    ! [B_112] :
      ( v2_funct_1(B_112)
      | ~ r1_tarski(k2_relat_1(B_112),'#skF_1')
      | ~ v2_funct_1(k5_relat_1(B_112,'#skF_5'))
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_40,c_507])).

tff(c_529,plain,(
    ! [B_2] :
      ( v2_funct_1(B_2)
      | ~ v2_funct_1(k5_relat_1(B_2,'#skF_5'))
      | ~ v1_funct_1(B_2)
      | ~ v5_relat_1(B_2,'#skF_1')
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_524])).

tff(c_594,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_587,c_529])).

tff(c_597,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_341,c_46,c_594])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_597])).

tff(c_600,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_607,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_299])).

tff(c_610,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_266])).

tff(c_611,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_600,c_265])).

tff(c_769,plain,(
    ! [D_148,A_144,B_149,C_145,E_146,F_147] :
      ( k1_partfun1(A_144,B_149,C_145,D_148,E_146,F_147) = k5_relat_1(E_146,F_147)
      | ~ m1_subset_1(F_147,k1_zfmisc_1(k2_zfmisc_1(C_145,D_148)))
      | ~ v1_funct_1(F_147)
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_149)))
      | ~ v1_funct_1(E_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_773,plain,(
    ! [A_144,B_149,E_146] :
      ( k1_partfun1(A_144,B_149,'#skF_4','#skF_4',E_146,'#skF_5') = k5_relat_1(E_146,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_149)))
      | ~ v1_funct_1(E_146) ) ),
    inference(resolution,[status(thm)],[c_611,c_769])).

tff(c_808,plain,(
    ! [A_156,B_157,E_158] :
      ( k1_partfun1(A_156,B_157,'#skF_4','#skF_4',E_158,'#skF_5') = k5_relat_1(E_158,'#skF_5')
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_funct_1(E_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_773])).

tff(c_811,plain,
    ( k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_610,c_808])).

tff(c_817,plain,(
    k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_811])).

tff(c_609,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_600,c_600,c_276])).

tff(c_821,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_609])).

tff(c_613,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_600,c_264])).

tff(c_615,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_249])).

tff(c_629,plain,(
    ! [B_16,C_17] :
      ( k1_relset_1('#skF_4',B_16,C_17) = '#skF_4'
      | ~ v1_funct_2(C_17,'#skF_4',B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_16))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_615,c_615,c_615,c_24])).

tff(c_633,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_611,c_629])).

tff(c_648,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_633])).

tff(c_604,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_600,c_309])).

tff(c_664,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_604])).

tff(c_752,plain,(
    ! [B_141,A_142] :
      ( v2_funct_1(B_141)
      | ~ r1_tarski(k2_relat_1(B_141),k1_relat_1(A_142))
      | ~ v2_funct_1(k5_relat_1(B_141,A_142))
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1(A_142)
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_755,plain,(
    ! [B_141] :
      ( v2_funct_1(B_141)
      | ~ r1_tarski(k2_relat_1(B_141),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_141,'#skF_5'))
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_752])).

tff(c_763,plain,(
    ! [B_143] :
      ( v2_funct_1(B_143)
      | ~ r1_tarski(k2_relat_1(B_143),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_143,'#skF_5'))
      | ~ v1_funct_1(B_143)
      | ~ v1_relat_1(B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_40,c_755])).

tff(c_768,plain,(
    ! [B_2] :
      ( v2_funct_1(B_2)
      | ~ v2_funct_1(k5_relat_1(B_2,'#skF_5'))
      | ~ v1_funct_1(B_2)
      | ~ v5_relat_1(B_2,'#skF_4')
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_763])).

tff(c_828,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_821,c_768])).

tff(c_831,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_607,c_46,c_828])).

tff(c_833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_831])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:22:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.44  
% 2.83/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.83/1.44  
% 2.83/1.44  %Foreground sorts:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Background operators:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Foreground operators:
% 2.83/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.83/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.44  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.83/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.83/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.83/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.44  
% 3.29/1.47  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 3.29/1.47  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.29/1.47  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.29/1.47  tff(f_88, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.29/1.47  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.29/1.47  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.29/1.47  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.29/1.47  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 3.29/1.47  tff(c_30, plain, (~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.29/1.47  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.29/1.47  tff(c_48, plain, (![C_25, A_26, B_27]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.29/1.47  tff(c_55, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_48])).
% 3.29/1.47  tff(c_67, plain, (![C_33, B_34, A_35]: (v5_relat_1(C_33, B_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_35, B_34))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.47  tff(c_74, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_67])).
% 3.29/1.47  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.29/1.47  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.29/1.47  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.29/1.47  tff(c_190, plain, (![D_66, B_67, C_63, F_65, A_62, E_64]: (k1_partfun1(A_62, B_67, C_63, D_66, E_64, F_65)=k5_relat_1(E_64, F_65) | ~m1_subset_1(F_65, k1_zfmisc_1(k2_zfmisc_1(C_63, D_66))) | ~v1_funct_1(F_65) | ~m1_subset_1(E_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_67))) | ~v1_funct_1(E_64))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.47  tff(c_194, plain, (![A_62, B_67, E_64]: (k1_partfun1(A_62, B_67, '#skF_2', '#skF_3', E_64, '#skF_5')=k5_relat_1(E_64, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_67))) | ~v1_funct_1(E_64))), inference(resolution, [status(thm)], [c_36, c_190])).
% 3.29/1.47  tff(c_222, plain, (![A_71, B_72, E_73]: (k1_partfun1(A_71, B_72, '#skF_2', '#skF_3', E_73, '#skF_5')=k5_relat_1(E_73, '#skF_5') | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_funct_1(E_73))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_194])).
% 3.29/1.47  tff(c_225, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_222])).
% 3.29/1.47  tff(c_231, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_225])).
% 3.29/1.47  tff(c_34, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.29/1.47  tff(c_235, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_34])).
% 3.29/1.47  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.47  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_48])).
% 3.29/1.47  tff(c_32, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.29/1.47  tff(c_47, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_32])).
% 3.29/1.47  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.29/1.47  tff(c_81, plain, (![A_38, B_39, C_40]: (k1_relset_1(A_38, B_39, C_40)=k1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/1.47  tff(c_89, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_81])).
% 3.29/1.47  tff(c_102, plain, (![B_48, A_49, C_50]: (k1_xboole_0=B_48 | k1_relset_1(A_49, B_48, C_50)=A_49 | ~v1_funct_2(C_50, A_49, B_48) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.29/1.47  tff(c_108, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_102])).
% 3.29/1.47  tff(c_114, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_89, c_108])).
% 3.29/1.47  tff(c_115, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_47, c_114])).
% 3.29/1.47  tff(c_149, plain, (![B_54, A_55]: (v2_funct_1(B_54) | ~r1_tarski(k2_relat_1(B_54), k1_relat_1(A_55)) | ~v2_funct_1(k5_relat_1(B_54, A_55)) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.29/1.47  tff(c_155, plain, (![B_54]: (v2_funct_1(B_54) | ~r1_tarski(k2_relat_1(B_54), '#skF_2') | ~v2_funct_1(k5_relat_1(B_54, '#skF_5')) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_149])).
% 3.29/1.47  tff(c_172, plain, (![B_58]: (v2_funct_1(B_58) | ~r1_tarski(k2_relat_1(B_58), '#skF_2') | ~v2_funct_1(k5_relat_1(B_58, '#skF_5')) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_40, c_155])).
% 3.29/1.47  tff(c_177, plain, (![B_2]: (v2_funct_1(B_2) | ~v2_funct_1(k5_relat_1(B_2, '#skF_5')) | ~v1_funct_1(B_2) | ~v5_relat_1(B_2, '#skF_2') | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_172])).
% 3.29/1.47  tff(c_242, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_235, c_177])).
% 3.29/1.47  tff(c_245, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_74, c_46, c_242])).
% 3.29/1.47  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_245])).
% 3.29/1.47  tff(c_249, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 3.29/1.47  tff(c_248, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 3.29/1.47  tff(c_254, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_249, c_248])).
% 3.29/1.47  tff(c_266, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_42])).
% 3.29/1.47  tff(c_267, plain, (![C_74, A_75, B_76]: (v1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.29/1.47  tff(c_274, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_266, c_267])).
% 3.29/1.47  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.29/1.47  tff(c_259, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_44])).
% 3.29/1.47  tff(c_18, plain, (![C_17, A_15]: (k1_xboole_0=C_17 | ~v1_funct_2(C_17, A_15, k1_xboole_0) | k1_xboole_0=A_15 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.29/1.47  tff(c_321, plain, (![C_91, A_92]: (C_91='#skF_3' | ~v1_funct_2(C_91, A_92, '#skF_3') | A_92='#skF_3' | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_249, c_249, c_249, c_18])).
% 3.29/1.47  tff(c_324, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_266, c_321])).
% 3.29/1.47  tff(c_330, plain, ('#skF_3'='#skF_4' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_259, c_324])).
% 3.29/1.47  tff(c_335, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_330])).
% 3.29/1.47  tff(c_292, plain, (![C_84, B_85, A_86]: (v5_relat_1(C_84, B_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.47  tff(c_299, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_266, c_292])).
% 3.29/1.47  tff(c_341, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_299])).
% 3.29/1.47  tff(c_344, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_266])).
% 3.29/1.47  tff(c_265, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_36])).
% 3.29/1.47  tff(c_345, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_335, c_265])).
% 3.29/1.47  tff(c_542, plain, (![A_116, B_121, D_120, C_117, F_119, E_118]: (k1_partfun1(A_116, B_121, C_117, D_120, E_118, F_119)=k5_relat_1(E_118, F_119) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_117, D_120))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_121))) | ~v1_funct_1(E_118))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.47  tff(c_546, plain, (![A_116, B_121, E_118]: (k1_partfun1(A_116, B_121, '#skF_1', '#skF_1', E_118, '#skF_5')=k5_relat_1(E_118, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_121))) | ~v1_funct_1(E_118))), inference(resolution, [status(thm)], [c_345, c_542])).
% 3.29/1.47  tff(c_574, plain, (![A_125, B_126, E_127]: (k1_partfun1(A_125, B_126, '#skF_1', '#skF_1', E_127, '#skF_5')=k5_relat_1(E_127, '#skF_5') | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_1(E_127))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_546])).
% 3.29/1.47  tff(c_577, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_344, c_574])).
% 3.29/1.47  tff(c_583, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_577])).
% 3.29/1.47  tff(c_276, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_254, c_34])).
% 3.29/1.47  tff(c_343, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_335, c_335, c_276])).
% 3.29/1.47  tff(c_587, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_583, c_343])).
% 3.29/1.47  tff(c_275, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_265, c_267])).
% 3.29/1.47  tff(c_264, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_38])).
% 3.29/1.47  tff(c_347, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_335, c_264])).
% 3.29/1.47  tff(c_349, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_335, c_249])).
% 3.29/1.47  tff(c_24, plain, (![B_16, C_17]: (k1_relset_1(k1_xboole_0, B_16, C_17)=k1_xboole_0 | ~v1_funct_2(C_17, k1_xboole_0, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_16))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.29/1.47  tff(c_388, plain, (![B_95, C_96]: (k1_relset_1('#skF_1', B_95, C_96)='#skF_1' | ~v1_funct_2(C_96, '#skF_1', B_95) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_95))))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_349, c_349, c_349, c_24])).
% 3.29/1.47  tff(c_391, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_345, c_388])).
% 3.29/1.47  tff(c_394, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_391])).
% 3.29/1.47  tff(c_301, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/1.47  tff(c_309, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_265, c_301])).
% 3.29/1.47  tff(c_338, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_335, c_309])).
% 3.29/1.47  tff(c_399, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_394, c_338])).
% 3.29/1.47  tff(c_501, plain, (![B_108, A_109]: (v2_funct_1(B_108) | ~r1_tarski(k2_relat_1(B_108), k1_relat_1(A_109)) | ~v2_funct_1(k5_relat_1(B_108, A_109)) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.29/1.47  tff(c_507, plain, (![B_108]: (v2_funct_1(B_108) | ~r1_tarski(k2_relat_1(B_108), '#skF_1') | ~v2_funct_1(k5_relat_1(B_108, '#skF_5')) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_501])).
% 3.29/1.47  tff(c_524, plain, (![B_112]: (v2_funct_1(B_112) | ~r1_tarski(k2_relat_1(B_112), '#skF_1') | ~v2_funct_1(k5_relat_1(B_112, '#skF_5')) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_40, c_507])).
% 3.29/1.47  tff(c_529, plain, (![B_2]: (v2_funct_1(B_2) | ~v2_funct_1(k5_relat_1(B_2, '#skF_5')) | ~v1_funct_1(B_2) | ~v5_relat_1(B_2, '#skF_1') | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_524])).
% 3.29/1.47  tff(c_594, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_587, c_529])).
% 3.29/1.47  tff(c_597, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_341, c_46, c_594])).
% 3.29/1.47  tff(c_599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_597])).
% 3.29/1.47  tff(c_600, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_330])).
% 3.29/1.47  tff(c_607, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_299])).
% 3.29/1.47  tff(c_610, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_266])).
% 3.29/1.47  tff(c_611, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_600, c_265])).
% 3.29/1.47  tff(c_769, plain, (![D_148, A_144, B_149, C_145, E_146, F_147]: (k1_partfun1(A_144, B_149, C_145, D_148, E_146, F_147)=k5_relat_1(E_146, F_147) | ~m1_subset_1(F_147, k1_zfmisc_1(k2_zfmisc_1(C_145, D_148))) | ~v1_funct_1(F_147) | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_149))) | ~v1_funct_1(E_146))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.47  tff(c_773, plain, (![A_144, B_149, E_146]: (k1_partfun1(A_144, B_149, '#skF_4', '#skF_4', E_146, '#skF_5')=k5_relat_1(E_146, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_149))) | ~v1_funct_1(E_146))), inference(resolution, [status(thm)], [c_611, c_769])).
% 3.29/1.47  tff(c_808, plain, (![A_156, B_157, E_158]: (k1_partfun1(A_156, B_157, '#skF_4', '#skF_4', E_158, '#skF_5')=k5_relat_1(E_158, '#skF_5') | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_1(E_158))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_773])).
% 3.29/1.47  tff(c_811, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_610, c_808])).
% 3.29/1.47  tff(c_817, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_811])).
% 3.29/1.47  tff(c_609, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_600, c_600, c_276])).
% 3.29/1.47  tff(c_821, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_817, c_609])).
% 3.29/1.47  tff(c_613, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_600, c_264])).
% 3.29/1.47  tff(c_615, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_600, c_249])).
% 3.29/1.47  tff(c_629, plain, (![B_16, C_17]: (k1_relset_1('#skF_4', B_16, C_17)='#skF_4' | ~v1_funct_2(C_17, '#skF_4', B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_16))))), inference(demodulation, [status(thm), theory('equality')], [c_615, c_615, c_615, c_615, c_24])).
% 3.29/1.47  tff(c_633, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_611, c_629])).
% 3.29/1.47  tff(c_648, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_613, c_633])).
% 3.29/1.47  tff(c_604, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_600, c_309])).
% 3.29/1.47  tff(c_664, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_648, c_604])).
% 3.29/1.47  tff(c_752, plain, (![B_141, A_142]: (v2_funct_1(B_141) | ~r1_tarski(k2_relat_1(B_141), k1_relat_1(A_142)) | ~v2_funct_1(k5_relat_1(B_141, A_142)) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1(A_142) | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.29/1.47  tff(c_755, plain, (![B_141]: (v2_funct_1(B_141) | ~r1_tarski(k2_relat_1(B_141), '#skF_4') | ~v2_funct_1(k5_relat_1(B_141, '#skF_5')) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_664, c_752])).
% 3.29/1.47  tff(c_763, plain, (![B_143]: (v2_funct_1(B_143) | ~r1_tarski(k2_relat_1(B_143), '#skF_4') | ~v2_funct_1(k5_relat_1(B_143, '#skF_5')) | ~v1_funct_1(B_143) | ~v1_relat_1(B_143))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_40, c_755])).
% 3.29/1.47  tff(c_768, plain, (![B_2]: (v2_funct_1(B_2) | ~v2_funct_1(k5_relat_1(B_2, '#skF_5')) | ~v1_funct_1(B_2) | ~v5_relat_1(B_2, '#skF_4') | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_763])).
% 3.29/1.47  tff(c_828, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_821, c_768])).
% 3.29/1.47  tff(c_831, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_607, c_46, c_828])).
% 3.29/1.47  tff(c_833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_831])).
% 3.29/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.47  
% 3.29/1.47  Inference rules
% 3.29/1.47  ----------------------
% 3.29/1.47  #Ref     : 0
% 3.29/1.47  #Sup     : 166
% 3.29/1.47  #Fact    : 0
% 3.29/1.47  #Define  : 0
% 3.29/1.47  #Split   : 3
% 3.29/1.47  #Chain   : 0
% 3.29/1.47  #Close   : 0
% 3.29/1.47  
% 3.29/1.47  Ordering : KBO
% 3.29/1.47  
% 3.29/1.47  Simplification rules
% 3.29/1.47  ----------------------
% 3.29/1.47  #Subsume      : 5
% 3.29/1.47  #Demod        : 203
% 3.29/1.47  #Tautology    : 105
% 3.29/1.47  #SimpNegUnit  : 7
% 3.29/1.47  #BackRed      : 37
% 3.29/1.47  
% 3.29/1.47  #Partial instantiations: 0
% 3.29/1.47  #Strategies tried      : 1
% 3.29/1.47  
% 3.29/1.47  Timing (in seconds)
% 3.29/1.47  ----------------------
% 3.29/1.47  Preprocessing        : 0.32
% 3.29/1.47  Parsing              : 0.17
% 3.29/1.47  CNF conversion       : 0.02
% 3.29/1.47  Main loop            : 0.37
% 3.29/1.47  Inferencing          : 0.14
% 3.29/1.47  Reduction            : 0.12
% 3.29/1.47  Demodulation         : 0.08
% 3.29/1.47  BG Simplification    : 0.02
% 3.29/1.47  Subsumption          : 0.06
% 3.29/1.47  Abstraction          : 0.01
% 3.29/1.47  MUC search           : 0.00
% 3.29/1.47  Cooper               : 0.00
% 3.29/1.47  Total                : 0.74
% 3.29/1.47  Index Insertion      : 0.00
% 3.29/1.47  Index Deletion       : 0.00
% 3.29/1.47  Index Matching       : 0.00
% 3.29/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
