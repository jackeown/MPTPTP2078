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
% DateTime   : Thu Dec  3 10:15:42 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.23s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 965 expanded)
%              Number of leaves         :   36 ( 317 expanded)
%              Depth                    :   14
%              Number of atoms          :  362 (2747 expanded)
%              Number of equality atoms :  106 ( 805 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_52,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_73,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_112,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_129,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_112])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_236,plain,(
    ! [A_76] :
      ( '#skF_2'(A_76) != '#skF_1'(A_76)
      | v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_239,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_236,c_73])).

tff(c_242,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_50,c_239])).

tff(c_437,plain,(
    ! [A_98] :
      ( k1_funct_1(A_98,'#skF_2'(A_98)) = k1_funct_1(A_98,'#skF_1'(A_98))
      | v2_funct_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_70,plain,(
    ! [D_42,C_41] :
      ( v2_funct_1('#skF_4')
      | D_42 = C_41
      | k1_funct_1('#skF_4',D_42) != k1_funct_1('#skF_4',C_41)
      | ~ r2_hidden(D_42,'#skF_3')
      | ~ r2_hidden(C_41,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_251,plain,(
    ! [D_42,C_41] :
      ( D_42 = C_41
      | k1_funct_1('#skF_4',D_42) != k1_funct_1('#skF_4',C_41)
      | ~ r2_hidden(D_42,'#skF_3')
      | ~ r2_hidden(C_41,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_70])).

tff(c_446,plain,(
    ! [D_42] :
      ( D_42 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_42) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_42,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_251])).

tff(c_455,plain,(
    ! [D_42] :
      ( D_42 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_42) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_42,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_50,c_446])).

tff(c_456,plain,(
    ! [D_42] :
      ( D_42 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_42) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_42,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_455])).

tff(c_627,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_456])).

tff(c_264,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_283,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_264])).

tff(c_306,plain,(
    ! [A_91,B_92,C_93] :
      ( m1_subset_1(k1_relset_1(A_91,B_92,C_93),k1_zfmisc_1(A_91))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_332,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_306])).

tff(c_344,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_332])).

tff(c_244,plain,(
    ! [A_80] :
      ( r2_hidden('#skF_2'(A_80),k1_relat_1(A_80))
      | v2_funct_1(A_80)
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1252,plain,(
    ! [A_182,A_183] :
      ( r2_hidden('#skF_2'(A_182),A_183)
      | ~ m1_subset_1(k1_relat_1(A_182),k1_zfmisc_1(A_183))
      | v2_funct_1(A_182)
      | ~ v1_funct_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(resolution,[status(thm)],[c_244,c_14])).

tff(c_1255,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_344,c_1252])).

tff(c_1265,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_50,c_1255])).

tff(c_1267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_627,c_1265])).

tff(c_1269,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_456])).

tff(c_443,plain,(
    ! [C_41] :
      ( C_41 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_41) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_41,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_251])).

tff(c_452,plain,(
    ! [C_41] :
      ( C_41 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_41) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_41,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_50,c_443])).

tff(c_453,plain,(
    ! [C_41] :
      ( C_41 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_41) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_41,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_452])).

tff(c_1386,plain,(
    ! [C_41] :
      ( C_41 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_41) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(C_41,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1269,c_453])).

tff(c_1389,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1386])).

tff(c_1390,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_1389])).

tff(c_257,plain,(
    ! [A_83] :
      ( r2_hidden('#skF_1'(A_83),k1_relat_1(A_83))
      | v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1917,plain,(
    ! [A_238,A_239] :
      ( r2_hidden('#skF_1'(A_238),A_239)
      | ~ m1_subset_1(k1_relat_1(A_238),k1_zfmisc_1(A_239))
      | v2_funct_1(A_238)
      | ~ v1_funct_1(A_238)
      | ~ v1_relat_1(A_238) ) ),
    inference(resolution,[status(thm)],[c_257,c_14])).

tff(c_1920,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_344,c_1917])).

tff(c_1930,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_50,c_1920])).

tff(c_1932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_1390,c_1930])).

tff(c_1933,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1934,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_54,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1978,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1934,c_54])).

tff(c_58,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1959,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1934,c_58])).

tff(c_2979,plain,(
    ! [D_355,C_356,B_357,A_358] :
      ( k1_funct_1(k2_funct_1(D_355),k1_funct_1(D_355,C_356)) = C_356
      | k1_xboole_0 = B_357
      | ~ r2_hidden(C_356,A_358)
      | ~ v2_funct_1(D_355)
      | ~ m1_subset_1(D_355,k1_zfmisc_1(k2_zfmisc_1(A_358,B_357)))
      | ~ v1_funct_2(D_355,A_358,B_357)
      | ~ v1_funct_1(D_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3027,plain,(
    ! [D_366,B_367] :
      ( k1_funct_1(k2_funct_1(D_366),k1_funct_1(D_366,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_367
      | ~ v2_funct_1(D_366)
      | ~ m1_subset_1(D_366,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_367)))
      | ~ v1_funct_2(D_366,'#skF_3',B_367)
      | ~ v1_funct_1(D_366) ) ),
    inference(resolution,[status(thm)],[c_1959,c_2979])).

tff(c_3035,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_3027])).

tff(c_3046,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1934,c_1978,c_3035])).

tff(c_3049,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3046])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2094,plain,(
    ! [C_263,A_264,B_265] :
      ( r2_hidden(C_263,A_264)
      | ~ r2_hidden(C_263,B_265)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(A_264)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2112,plain,(
    ! [A_269] :
      ( r2_hidden('#skF_5',A_269)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_269)) ) ),
    inference(resolution,[status(thm)],[c_1959,c_2094])).

tff(c_2117,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_5',B_11)
      | ~ r1_tarski('#skF_3',B_11) ) ),
    inference(resolution,[status(thm)],[c_20,c_2112])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2122,plain,(
    ! [A_271,C_272,B_273] :
      ( m1_subset_1(A_271,C_272)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(C_272))
      | ~ r2_hidden(A_271,B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2132,plain,(
    ! [A_274,A_275] :
      ( m1_subset_1(A_274,A_275)
      | ~ r2_hidden(A_274,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_2122])).

tff(c_2139,plain,(
    ! [A_275] :
      ( m1_subset_1('#skF_5',A_275)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2117,c_2132])).

tff(c_2141,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2139])).

tff(c_3066,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3049,c_2141])).

tff(c_3079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3066])).

tff(c_3081,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3046])).

tff(c_3080,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3046])).

tff(c_56,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1961,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1934,c_56])).

tff(c_3161,plain,(
    ! [D_377,B_378] :
      ( k1_funct_1(k2_funct_1(D_377),k1_funct_1(D_377,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_378
      | ~ v2_funct_1(D_377)
      | ~ m1_subset_1(D_377,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_378)))
      | ~ v1_funct_2(D_377,'#skF_3',B_378)
      | ~ v1_funct_1(D_377) ) ),
    inference(resolution,[status(thm)],[c_1961,c_2979])).

tff(c_3169,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_3161])).

tff(c_3180,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1934,c_3080,c_3169])).

tff(c_3182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3081,c_1933,c_3180])).

tff(c_3184,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2139])).

tff(c_1963,plain,(
    ! [A_245,B_246] :
      ( r1_tarski(A_245,B_246)
      | ~ m1_subset_1(A_245,k1_zfmisc_1(B_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1975,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(resolution,[status(thm)],[c_16,c_1963])).

tff(c_2027,plain,(
    ! [B_253,A_254] :
      ( B_253 = A_254
      | ~ r1_tarski(B_253,A_254)
      | ~ r1_tarski(A_254,B_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2035,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1975,c_2027])).

tff(c_3214,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3184,c_2035])).

tff(c_3226,plain,(
    ! [A_9] : r1_tarski('#skF_3',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3214,c_1975])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3229,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3214,c_3214,c_10])).

tff(c_1974,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_1963])).

tff(c_2034,plain,
    ( k2_zfmisc_1('#skF_3','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1974,c_2027])).

tff(c_2093,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2034])).

tff(c_3280,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3229,c_2093])).

tff(c_3285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_3280])).

tff(c_3286,plain,(
    k2_zfmisc_1('#skF_3','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2034])).

tff(c_3296,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3286,c_46])).

tff(c_4146,plain,(
    ! [D_475,C_476,B_477,A_478] :
      ( k1_funct_1(k2_funct_1(D_475),k1_funct_1(D_475,C_476)) = C_476
      | k1_xboole_0 = B_477
      | ~ r2_hidden(C_476,A_478)
      | ~ v2_funct_1(D_475)
      | ~ m1_subset_1(D_475,k1_zfmisc_1(k2_zfmisc_1(A_478,B_477)))
      | ~ v1_funct_2(D_475,A_478,B_477)
      | ~ v1_funct_1(D_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4530,plain,(
    ! [D_504,B_505] :
      ( k1_funct_1(k2_funct_1(D_504),k1_funct_1(D_504,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_505
      | ~ v2_funct_1(D_504)
      | ~ m1_subset_1(D_504,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_505)))
      | ~ v1_funct_2(D_504,'#skF_3',B_505)
      | ~ v1_funct_1(D_504) ) ),
    inference(resolution,[status(thm)],[c_1961,c_4146])).

tff(c_4535,plain,(
    ! [D_504] :
      ( k1_funct_1(k2_funct_1(D_504),k1_funct_1(D_504,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = '#skF_3'
      | ~ v2_funct_1(D_504)
      | ~ m1_subset_1(D_504,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_504,'#skF_3','#skF_3')
      | ~ v1_funct_1(D_504) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3286,c_4530])).

tff(c_4741,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4535])).

tff(c_3288,plain,(
    ! [C_385,A_386,B_387] :
      ( r2_hidden(C_385,A_386)
      | ~ r2_hidden(C_385,B_387)
      | ~ m1_subset_1(B_387,k1_zfmisc_1(A_386)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3360,plain,(
    ! [A_393] :
      ( r2_hidden('#skF_6',A_393)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_393)) ) ),
    inference(resolution,[status(thm)],[c_1961,c_3288])).

tff(c_3365,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_6',B_11)
      | ~ r1_tarski('#skF_3',B_11) ) ),
    inference(resolution,[status(thm)],[c_20,c_3360])).

tff(c_3371,plain,(
    ! [A_395,C_396,B_397] :
      ( m1_subset_1(A_395,C_396)
      | ~ m1_subset_1(B_397,k1_zfmisc_1(C_396))
      | ~ r2_hidden(A_395,B_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3381,plain,(
    ! [A_398,A_399] :
      ( m1_subset_1(A_398,A_399)
      | ~ r2_hidden(A_398,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_3371])).

tff(c_3388,plain,(
    ! [A_399] :
      ( m1_subset_1('#skF_6',A_399)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3365,c_3381])).

tff(c_3401,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3388])).

tff(c_4764,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4741,c_3401])).

tff(c_4778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4764])).

tff(c_9734,plain,(
    ! [D_778] :
      ( k1_funct_1(k2_funct_1(D_778),k1_funct_1(D_778,'#skF_6')) = '#skF_6'
      | ~ v2_funct_1(D_778)
      | ~ m1_subset_1(D_778,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_778,'#skF_3','#skF_3')
      | ~ v1_funct_1(D_778) ) ),
    inference(splitRight,[status(thm)],[c_4535])).

tff(c_4780,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4535])).

tff(c_4194,plain,(
    ! [D_483,B_484] :
      ( k1_funct_1(k2_funct_1(D_483),k1_funct_1(D_483,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_484
      | ~ v2_funct_1(D_483)
      | ~ m1_subset_1(D_483,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_484)))
      | ~ v1_funct_2(D_483,'#skF_3',B_484)
      | ~ v1_funct_1(D_483) ) ),
    inference(resolution,[status(thm)],[c_1959,c_4146])).

tff(c_4199,plain,(
    ! [D_483] :
      ( k1_funct_1(k2_funct_1(D_483),k1_funct_1(D_483,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = '#skF_3'
      | ~ v2_funct_1(D_483)
      | ~ m1_subset_1(D_483,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_483,'#skF_3','#skF_3')
      | ~ v1_funct_1(D_483) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3286,c_4194])).

tff(c_4867,plain,(
    ! [D_536] :
      ( k1_funct_1(k2_funct_1(D_536),k1_funct_1(D_536,'#skF_5')) = '#skF_5'
      | ~ v2_funct_1(D_536)
      | ~ m1_subset_1(D_536,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_536,'#skF_3','#skF_3')
      | ~ v1_funct_1(D_536) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4780,c_4199])).

tff(c_4894,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | ~ v2_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1978,c_4867])).

tff(c_4900,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3296,c_1934,c_4894])).

tff(c_9760,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v2_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9734,c_4900])).

tff(c_9807,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3296,c_1934,c_9760])).

tff(c_9809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1933,c_9807])).

tff(c_9811,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3388])).

tff(c_9847,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9811,c_2035])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3301,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3286,c_8])).

tff(c_3348,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3301])).

tff(c_9858,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9847,c_3348])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9941,plain,(
    ! [B_786] : k2_zfmisc_1('#skF_3',B_786) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9847,c_9847,c_12])).

tff(c_9945,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9941,c_3286])).

tff(c_9958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9858,c_9945])).

tff(c_9960,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3301])).

tff(c_9959,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3301])).

tff(c_9992,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9960,c_9960,c_9959])).

tff(c_9993,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9992])).

tff(c_9996,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9993,c_1959])).

tff(c_10053,plain,(
    ! [A_793] : m1_subset_1('#skF_4',k1_zfmisc_1(A_793)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9960,c_16])).

tff(c_22,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10099,plain,(
    ! [A_797,A_798] :
      ( m1_subset_1(A_797,A_798)
      | ~ r2_hidden(A_797,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10053,c_22])).

tff(c_10107,plain,(
    ! [A_799] : m1_subset_1('#skF_5',A_799) ),
    inference(resolution,[status(thm)],[c_9996,c_10099])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10154,plain,(
    ! [B_802] : r1_tarski('#skF_5',B_802) ),
    inference(resolution,[status(thm)],[c_10107,c_18])).

tff(c_9963,plain,(
    ! [A_9] :
      ( A_9 = '#skF_4'
      | ~ r1_tarski(A_9,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9960,c_9960,c_2035])).

tff(c_10169,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10154,c_9963])).

tff(c_10193,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10169,c_1933])).

tff(c_9995,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9993,c_1961])).

tff(c_10129,plain,(
    ! [A_800] : m1_subset_1('#skF_6',A_800) ),
    inference(resolution,[status(thm)],[c_9995,c_10099])).

tff(c_10200,plain,(
    ! [B_804] : r1_tarski('#skF_6',B_804) ),
    inference(resolution,[status(thm)],[c_10129,c_18])).

tff(c_10204,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10200,c_9963])).

tff(c_10218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10193,c_10204])).

tff(c_10219,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9992])).

tff(c_10220,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9992])).

tff(c_10230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10219,c_10220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.03/2.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.23/2.98  
% 8.23/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.23/2.99  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 8.23/2.99  
% 8.23/2.99  %Foreground sorts:
% 8.23/2.99  
% 8.23/2.99  
% 8.23/2.99  %Background operators:
% 8.23/2.99  
% 8.23/2.99  
% 8.23/2.99  %Foreground operators:
% 8.23/2.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.23/2.99  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.23/2.99  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.23/2.99  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.23/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.23/2.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.23/2.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.23/2.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.23/2.99  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.23/2.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.23/2.99  tff('#skF_5', type, '#skF_5': $i).
% 8.23/2.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.23/2.99  tff('#skF_6', type, '#skF_6': $i).
% 8.23/2.99  tff('#skF_3', type, '#skF_3': $i).
% 8.23/2.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.23/2.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.23/2.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.23/2.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.23/2.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.23/2.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.23/2.99  tff('#skF_4', type, '#skF_4': $i).
% 8.23/2.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.23/2.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.23/2.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.23/2.99  
% 8.23/3.01  tff(f_127, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 8.23/3.01  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.23/3.01  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 8.23/3.01  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.23/3.01  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 8.23/3.01  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 8.23/3.01  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.23/3.01  tff(f_109, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 8.23/3.01  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.23/3.01  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.23/3.01  tff(f_56, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 8.23/3.01  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.23/3.01  tff(c_52, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.23/3.01  tff(c_73, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 8.23/3.01  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.23/3.01  tff(c_112, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.23/3.01  tff(c_129, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_112])).
% 8.23/3.01  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.23/3.01  tff(c_236, plain, (![A_76]: ('#skF_2'(A_76)!='#skF_1'(A_76) | v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.23/3.01  tff(c_239, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_236, c_73])).
% 8.23/3.01  tff(c_242, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_50, c_239])).
% 8.23/3.01  tff(c_437, plain, (![A_98]: (k1_funct_1(A_98, '#skF_2'(A_98))=k1_funct_1(A_98, '#skF_1'(A_98)) | v2_funct_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.23/3.01  tff(c_70, plain, (![D_42, C_41]: (v2_funct_1('#skF_4') | D_42=C_41 | k1_funct_1('#skF_4', D_42)!=k1_funct_1('#skF_4', C_41) | ~r2_hidden(D_42, '#skF_3') | ~r2_hidden(C_41, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.23/3.01  tff(c_251, plain, (![D_42, C_41]: (D_42=C_41 | k1_funct_1('#skF_4', D_42)!=k1_funct_1('#skF_4', C_41) | ~r2_hidden(D_42, '#skF_3') | ~r2_hidden(C_41, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_73, c_70])).
% 8.23/3.01  tff(c_446, plain, (![D_42]: (D_42='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_42)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_42, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_437, c_251])).
% 8.23/3.01  tff(c_455, plain, (![D_42]: (D_42='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_42)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_42, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_50, c_446])).
% 8.23/3.01  tff(c_456, plain, (![D_42]: (D_42='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_42)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_42, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_73, c_455])).
% 8.23/3.01  tff(c_627, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_456])).
% 8.23/3.01  tff(c_264, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.23/3.01  tff(c_283, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_264])).
% 8.23/3.01  tff(c_306, plain, (![A_91, B_92, C_93]: (m1_subset_1(k1_relset_1(A_91, B_92, C_93), k1_zfmisc_1(A_91)) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.23/3.01  tff(c_332, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_283, c_306])).
% 8.23/3.01  tff(c_344, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_332])).
% 8.23/3.01  tff(c_244, plain, (![A_80]: (r2_hidden('#skF_2'(A_80), k1_relat_1(A_80)) | v2_funct_1(A_80) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.23/3.01  tff(c_14, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.23/3.01  tff(c_1252, plain, (![A_182, A_183]: (r2_hidden('#skF_2'(A_182), A_183) | ~m1_subset_1(k1_relat_1(A_182), k1_zfmisc_1(A_183)) | v2_funct_1(A_182) | ~v1_funct_1(A_182) | ~v1_relat_1(A_182))), inference(resolution, [status(thm)], [c_244, c_14])).
% 8.23/3.01  tff(c_1255, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_344, c_1252])).
% 8.23/3.01  tff(c_1265, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_50, c_1255])).
% 8.23/3.01  tff(c_1267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_627, c_1265])).
% 8.23/3.01  tff(c_1269, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_456])).
% 8.23/3.01  tff(c_443, plain, (![C_41]: (C_41='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_41)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_41, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_437, c_251])).
% 8.23/3.01  tff(c_452, plain, (![C_41]: (C_41='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_41)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_41, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_50, c_443])).
% 8.23/3.01  tff(c_453, plain, (![C_41]: (C_41='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_41)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_41, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_73, c_452])).
% 8.23/3.01  tff(c_1386, plain, (![C_41]: (C_41='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_41)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(C_41, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1269, c_453])).
% 8.23/3.01  tff(c_1389, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_1386])).
% 8.23/3.01  tff(c_1390, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_242, c_1389])).
% 8.23/3.01  tff(c_257, plain, (![A_83]: (r2_hidden('#skF_1'(A_83), k1_relat_1(A_83)) | v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.23/3.01  tff(c_1917, plain, (![A_238, A_239]: (r2_hidden('#skF_1'(A_238), A_239) | ~m1_subset_1(k1_relat_1(A_238), k1_zfmisc_1(A_239)) | v2_funct_1(A_238) | ~v1_funct_1(A_238) | ~v1_relat_1(A_238))), inference(resolution, [status(thm)], [c_257, c_14])).
% 8.23/3.01  tff(c_1920, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_344, c_1917])).
% 8.23/3.01  tff(c_1930, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_50, c_1920])).
% 8.23/3.01  tff(c_1932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_1390, c_1930])).
% 8.23/3.01  tff(c_1933, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 8.23/3.01  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.23/3.01  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.23/3.01  tff(c_1934, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 8.23/3.01  tff(c_54, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.23/3.01  tff(c_1978, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1934, c_54])).
% 8.23/3.01  tff(c_58, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.23/3.01  tff(c_1959, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1934, c_58])).
% 8.23/3.01  tff(c_2979, plain, (![D_355, C_356, B_357, A_358]: (k1_funct_1(k2_funct_1(D_355), k1_funct_1(D_355, C_356))=C_356 | k1_xboole_0=B_357 | ~r2_hidden(C_356, A_358) | ~v2_funct_1(D_355) | ~m1_subset_1(D_355, k1_zfmisc_1(k2_zfmisc_1(A_358, B_357))) | ~v1_funct_2(D_355, A_358, B_357) | ~v1_funct_1(D_355))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.23/3.01  tff(c_3027, plain, (![D_366, B_367]: (k1_funct_1(k2_funct_1(D_366), k1_funct_1(D_366, '#skF_5'))='#skF_5' | k1_xboole_0=B_367 | ~v2_funct_1(D_366) | ~m1_subset_1(D_366, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_367))) | ~v1_funct_2(D_366, '#skF_3', B_367) | ~v1_funct_1(D_366))), inference(resolution, [status(thm)], [c_1959, c_2979])).
% 8.23/3.01  tff(c_3035, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_3027])).
% 8.23/3.01  tff(c_3046, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1934, c_1978, c_3035])).
% 8.23/3.01  tff(c_3049, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3046])).
% 8.23/3.01  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.23/3.01  tff(c_2094, plain, (![C_263, A_264, B_265]: (r2_hidden(C_263, A_264) | ~r2_hidden(C_263, B_265) | ~m1_subset_1(B_265, k1_zfmisc_1(A_264)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.23/3.01  tff(c_2112, plain, (![A_269]: (r2_hidden('#skF_5', A_269) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_269)))), inference(resolution, [status(thm)], [c_1959, c_2094])).
% 8.23/3.01  tff(c_2117, plain, (![B_11]: (r2_hidden('#skF_5', B_11) | ~r1_tarski('#skF_3', B_11))), inference(resolution, [status(thm)], [c_20, c_2112])).
% 8.23/3.01  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.23/3.01  tff(c_2122, plain, (![A_271, C_272, B_273]: (m1_subset_1(A_271, C_272) | ~m1_subset_1(B_273, k1_zfmisc_1(C_272)) | ~r2_hidden(A_271, B_273))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.23/3.01  tff(c_2132, plain, (![A_274, A_275]: (m1_subset_1(A_274, A_275) | ~r2_hidden(A_274, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_2122])).
% 8.23/3.01  tff(c_2139, plain, (![A_275]: (m1_subset_1('#skF_5', A_275) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_2117, c_2132])).
% 8.23/3.01  tff(c_2141, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2139])).
% 8.23/3.01  tff(c_3066, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3049, c_2141])).
% 8.23/3.01  tff(c_3079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3066])).
% 8.23/3.01  tff(c_3081, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3046])).
% 8.23/3.01  tff(c_3080, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_3046])).
% 8.23/3.01  tff(c_56, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.23/3.01  tff(c_1961, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1934, c_56])).
% 8.23/3.01  tff(c_3161, plain, (![D_377, B_378]: (k1_funct_1(k2_funct_1(D_377), k1_funct_1(D_377, '#skF_6'))='#skF_6' | k1_xboole_0=B_378 | ~v2_funct_1(D_377) | ~m1_subset_1(D_377, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_378))) | ~v1_funct_2(D_377, '#skF_3', B_378) | ~v1_funct_1(D_377))), inference(resolution, [status(thm)], [c_1961, c_2979])).
% 8.23/3.01  tff(c_3169, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_3161])).
% 8.23/3.01  tff(c_3180, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1934, c_3080, c_3169])).
% 8.23/3.01  tff(c_3182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3081, c_1933, c_3180])).
% 8.23/3.01  tff(c_3184, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2139])).
% 8.23/3.01  tff(c_1963, plain, (![A_245, B_246]: (r1_tarski(A_245, B_246) | ~m1_subset_1(A_245, k1_zfmisc_1(B_246)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.23/3.01  tff(c_1975, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(resolution, [status(thm)], [c_16, c_1963])).
% 8.23/3.01  tff(c_2027, plain, (![B_253, A_254]: (B_253=A_254 | ~r1_tarski(B_253, A_254) | ~r1_tarski(A_254, B_253))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.23/3.01  tff(c_2035, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_1975, c_2027])).
% 8.23/3.01  tff(c_3214, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3184, c_2035])).
% 8.23/3.01  tff(c_3226, plain, (![A_9]: (r1_tarski('#skF_3', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_3214, c_1975])).
% 8.23/3.01  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.23/3.01  tff(c_3229, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3214, c_3214, c_10])).
% 8.23/3.01  tff(c_1974, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_1963])).
% 8.23/3.01  tff(c_2034, plain, (k2_zfmisc_1('#skF_3', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_1974, c_2027])).
% 8.23/3.01  tff(c_2093, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2034])).
% 8.23/3.01  tff(c_3280, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3229, c_2093])).
% 8.23/3.01  tff(c_3285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3226, c_3280])).
% 8.23/3.01  tff(c_3286, plain, (k2_zfmisc_1('#skF_3', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2034])).
% 8.23/3.01  tff(c_3296, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3286, c_46])).
% 8.23/3.01  tff(c_4146, plain, (![D_475, C_476, B_477, A_478]: (k1_funct_1(k2_funct_1(D_475), k1_funct_1(D_475, C_476))=C_476 | k1_xboole_0=B_477 | ~r2_hidden(C_476, A_478) | ~v2_funct_1(D_475) | ~m1_subset_1(D_475, k1_zfmisc_1(k2_zfmisc_1(A_478, B_477))) | ~v1_funct_2(D_475, A_478, B_477) | ~v1_funct_1(D_475))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.23/3.01  tff(c_4530, plain, (![D_504, B_505]: (k1_funct_1(k2_funct_1(D_504), k1_funct_1(D_504, '#skF_6'))='#skF_6' | k1_xboole_0=B_505 | ~v2_funct_1(D_504) | ~m1_subset_1(D_504, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_505))) | ~v1_funct_2(D_504, '#skF_3', B_505) | ~v1_funct_1(D_504))), inference(resolution, [status(thm)], [c_1961, c_4146])).
% 8.23/3.01  tff(c_4535, plain, (![D_504]: (k1_funct_1(k2_funct_1(D_504), k1_funct_1(D_504, '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1(D_504) | ~m1_subset_1(D_504, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_504, '#skF_3', '#skF_3') | ~v1_funct_1(D_504))), inference(superposition, [status(thm), theory('equality')], [c_3286, c_4530])).
% 8.23/3.01  tff(c_4741, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4535])).
% 8.23/3.01  tff(c_3288, plain, (![C_385, A_386, B_387]: (r2_hidden(C_385, A_386) | ~r2_hidden(C_385, B_387) | ~m1_subset_1(B_387, k1_zfmisc_1(A_386)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.23/3.01  tff(c_3360, plain, (![A_393]: (r2_hidden('#skF_6', A_393) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_393)))), inference(resolution, [status(thm)], [c_1961, c_3288])).
% 8.23/3.01  tff(c_3365, plain, (![B_11]: (r2_hidden('#skF_6', B_11) | ~r1_tarski('#skF_3', B_11))), inference(resolution, [status(thm)], [c_20, c_3360])).
% 8.23/3.01  tff(c_3371, plain, (![A_395, C_396, B_397]: (m1_subset_1(A_395, C_396) | ~m1_subset_1(B_397, k1_zfmisc_1(C_396)) | ~r2_hidden(A_395, B_397))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.23/3.01  tff(c_3381, plain, (![A_398, A_399]: (m1_subset_1(A_398, A_399) | ~r2_hidden(A_398, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_3371])).
% 8.23/3.01  tff(c_3388, plain, (![A_399]: (m1_subset_1('#skF_6', A_399) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_3365, c_3381])).
% 8.23/3.01  tff(c_3401, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3388])).
% 8.23/3.01  tff(c_4764, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4741, c_3401])).
% 8.23/3.01  tff(c_4778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4764])).
% 8.23/3.01  tff(c_9734, plain, (![D_778]: (k1_funct_1(k2_funct_1(D_778), k1_funct_1(D_778, '#skF_6'))='#skF_6' | ~v2_funct_1(D_778) | ~m1_subset_1(D_778, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_778, '#skF_3', '#skF_3') | ~v1_funct_1(D_778))), inference(splitRight, [status(thm)], [c_4535])).
% 8.23/3.01  tff(c_4780, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4535])).
% 8.23/3.01  tff(c_4194, plain, (![D_483, B_484]: (k1_funct_1(k2_funct_1(D_483), k1_funct_1(D_483, '#skF_5'))='#skF_5' | k1_xboole_0=B_484 | ~v2_funct_1(D_483) | ~m1_subset_1(D_483, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_484))) | ~v1_funct_2(D_483, '#skF_3', B_484) | ~v1_funct_1(D_483))), inference(resolution, [status(thm)], [c_1959, c_4146])).
% 8.23/3.01  tff(c_4199, plain, (![D_483]: (k1_funct_1(k2_funct_1(D_483), k1_funct_1(D_483, '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1(D_483) | ~m1_subset_1(D_483, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_483, '#skF_3', '#skF_3') | ~v1_funct_1(D_483))), inference(superposition, [status(thm), theory('equality')], [c_3286, c_4194])).
% 8.23/3.01  tff(c_4867, plain, (![D_536]: (k1_funct_1(k2_funct_1(D_536), k1_funct_1(D_536, '#skF_5'))='#skF_5' | ~v2_funct_1(D_536) | ~m1_subset_1(D_536, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_536, '#skF_3', '#skF_3') | ~v1_funct_1(D_536))), inference(negUnitSimplification, [status(thm)], [c_4780, c_4199])).
% 8.23/3.01  tff(c_4894, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | ~v2_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1978, c_4867])).
% 8.23/3.01  tff(c_4900, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3296, c_1934, c_4894])).
% 8.23/3.01  tff(c_9760, plain, ('#skF_5'='#skF_6' | ~v2_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9734, c_4900])).
% 8.23/3.01  tff(c_9807, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3296, c_1934, c_9760])).
% 8.23/3.01  tff(c_9809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1933, c_9807])).
% 8.23/3.01  tff(c_9811, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3388])).
% 8.23/3.01  tff(c_9847, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_9811, c_2035])).
% 8.23/3.01  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.23/3.01  tff(c_3301, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3286, c_8])).
% 8.23/3.01  tff(c_3348, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_3301])).
% 8.23/3.01  tff(c_9858, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9847, c_3348])).
% 8.23/3.01  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.23/3.01  tff(c_9941, plain, (![B_786]: (k2_zfmisc_1('#skF_3', B_786)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9847, c_9847, c_12])).
% 8.23/3.01  tff(c_9945, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_9941, c_3286])).
% 8.23/3.01  tff(c_9958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9858, c_9945])).
% 8.23/3.01  tff(c_9960, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3301])).
% 8.23/3.01  tff(c_9959, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3301])).
% 8.23/3.01  tff(c_9992, plain, ('#skF_3'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9960, c_9960, c_9959])).
% 8.23/3.01  tff(c_9993, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_9992])).
% 8.23/3.01  tff(c_9996, plain, (r2_hidden('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9993, c_1959])).
% 8.23/3.01  tff(c_10053, plain, (![A_793]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_793)))), inference(demodulation, [status(thm), theory('equality')], [c_9960, c_16])).
% 8.23/3.01  tff(c_22, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.23/3.01  tff(c_10099, plain, (![A_797, A_798]: (m1_subset_1(A_797, A_798) | ~r2_hidden(A_797, '#skF_4'))), inference(resolution, [status(thm)], [c_10053, c_22])).
% 8.23/3.01  tff(c_10107, plain, (![A_799]: (m1_subset_1('#skF_5', A_799))), inference(resolution, [status(thm)], [c_9996, c_10099])).
% 8.23/3.01  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.23/3.01  tff(c_10154, plain, (![B_802]: (r1_tarski('#skF_5', B_802))), inference(resolution, [status(thm)], [c_10107, c_18])).
% 8.23/3.01  tff(c_9963, plain, (![A_9]: (A_9='#skF_4' | ~r1_tarski(A_9, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9960, c_9960, c_2035])).
% 8.23/3.01  tff(c_10169, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_10154, c_9963])).
% 8.23/3.01  tff(c_10193, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10169, c_1933])).
% 8.23/3.01  tff(c_9995, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9993, c_1961])).
% 8.23/3.01  tff(c_10129, plain, (![A_800]: (m1_subset_1('#skF_6', A_800))), inference(resolution, [status(thm)], [c_9995, c_10099])).
% 8.23/3.01  tff(c_10200, plain, (![B_804]: (r1_tarski('#skF_6', B_804))), inference(resolution, [status(thm)], [c_10129, c_18])).
% 8.23/3.01  tff(c_10204, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_10200, c_9963])).
% 8.23/3.01  tff(c_10218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10193, c_10204])).
% 8.23/3.01  tff(c_10219, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_9992])).
% 8.23/3.01  tff(c_10220, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_9992])).
% 8.23/3.01  tff(c_10230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10219, c_10220])).
% 8.23/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.23/3.01  
% 8.23/3.01  Inference rules
% 8.23/3.01  ----------------------
% 8.23/3.01  #Ref     : 8
% 8.23/3.01  #Sup     : 2215
% 8.23/3.01  #Fact    : 0
% 8.23/3.01  #Define  : 0
% 8.23/3.01  #Split   : 29
% 8.23/3.01  #Chain   : 0
% 8.23/3.01  #Close   : 0
% 8.23/3.01  
% 8.23/3.01  Ordering : KBO
% 8.23/3.01  
% 8.23/3.01  Simplification rules
% 8.23/3.01  ----------------------
% 8.23/3.01  #Subsume      : 459
% 8.23/3.01  #Demod        : 3280
% 8.23/3.01  #Tautology    : 822
% 8.23/3.01  #SimpNegUnit  : 45
% 8.23/3.01  #BackRed      : 135
% 8.23/3.01  
% 8.23/3.01  #Partial instantiations: 0
% 8.23/3.01  #Strategies tried      : 1
% 8.23/3.02  
% 8.23/3.02  Timing (in seconds)
% 8.23/3.02  ----------------------
% 8.23/3.02  Preprocessing        : 0.32
% 8.23/3.02  Parsing              : 0.16
% 8.23/3.02  CNF conversion       : 0.02
% 8.23/3.02  Main loop            : 1.83
% 8.23/3.02  Inferencing          : 0.56
% 8.23/3.02  Reduction            : 0.71
% 8.23/3.02  Demodulation         : 0.54
% 8.23/3.02  BG Simplification    : 0.07
% 8.23/3.02  Subsumption          : 0.37
% 8.23/3.02  Abstraction          : 0.08
% 8.23/3.02  MUC search           : 0.00
% 8.23/3.02  Cooper               : 0.00
% 8.23/3.02  Total                : 2.22
% 8.23/3.02  Index Insertion      : 0.00
% 8.23/3.02  Index Deletion       : 0.00
% 8.23/3.02  Index Matching       : 0.00
% 8.23/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
