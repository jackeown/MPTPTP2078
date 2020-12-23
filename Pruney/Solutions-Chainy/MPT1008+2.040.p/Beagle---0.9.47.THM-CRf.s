%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:31 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 229 expanded)
%              Number of leaves         :   46 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  169 ( 468 expanded)
%              Number of equality atoms :   82 ( 208 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_138,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_137,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_145,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_137])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_38,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_154,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_145,c_38])).

tff(c_166,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_309,plain,(
    ! [B_112,A_113] :
      ( k1_tarski(k1_funct_1(B_112,A_113)) = k2_relat_1(B_112)
      | k1_tarski(A_113) != k1_relat_1(B_112)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_287,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_295,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_287])).

tff(c_70,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_304,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_70])).

tff(c_315,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_304])).

tff(c_328,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_78,c_315])).

tff(c_236,plain,(
    ! [C_97,A_98,B_99] :
      ( v4_relat_1(C_97,A_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_244,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_236])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(B_22),A_21)
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_546,plain,(
    ! [B_151,C_152,A_153] :
      ( k2_tarski(B_151,C_152) = A_153
      | k1_tarski(C_152) = A_153
      | k1_tarski(B_151) = A_153
      | k1_xboole_0 = A_153
      | ~ r1_tarski(A_153,k2_tarski(B_151,C_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_567,plain,(
    ! [A_8,A_153] :
      ( k2_tarski(A_8,A_8) = A_153
      | k1_tarski(A_8) = A_153
      | k1_tarski(A_8) = A_153
      | k1_xboole_0 = A_153
      | ~ r1_tarski(A_153,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_546])).

tff(c_971,plain,(
    ! [A_231,A_232] :
      ( k1_tarski(A_231) = A_232
      | k1_tarski(A_231) = A_232
      | k1_tarski(A_231) = A_232
      | k1_xboole_0 = A_232
      | ~ r1_tarski(A_232,k1_tarski(A_231)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_567])).

tff(c_1009,plain,(
    ! [A_236,B_237] :
      ( k1_tarski(A_236) = k1_relat_1(B_237)
      | k1_relat_1(B_237) = k1_xboole_0
      | ~ v4_relat_1(B_237,k1_tarski(A_236))
      | ~ v1_relat_1(B_237) ) ),
    inference(resolution,[status(thm)],[c_34,c_971])).

tff(c_1019,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_244,c_1009])).

tff(c_1025,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_1019])).

tff(c_1027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_328,c_1025])).

tff(c_1028,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_1029,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_1044,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_1029])).

tff(c_1274,plain,(
    ! [B_289,A_290] :
      ( k1_tarski(k1_funct_1(B_289,A_290)) = k2_relat_1(B_289)
      | k1_tarski(A_290) != k1_relat_1(B_289)
      | ~ v1_funct_1(B_289)
      | ~ v1_relat_1(B_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1036,plain,(
    ! [A_17] : m1_subset_1('#skF_6',k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_28])).

tff(c_1231,plain,(
    ! [A_282,B_283,C_284] :
      ( k2_relset_1(A_282,B_283,C_284) = k2_relat_1(C_284)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1236,plain,(
    ! [A_282,B_283] : k2_relset_1(A_282,B_283,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1036,c_1231])).

tff(c_1237,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1236,c_70])).

tff(c_1280,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1274,c_1237])).

tff(c_1293,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_78,c_1044,c_1280])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1038,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_72])).

tff(c_76,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_68,plain,(
    ! [B_51,A_50,C_52] :
      ( k1_xboole_0 = B_51
      | k1_relset_1(A_50,B_51,C_52) = A_50
      | ~ v1_funct_2(C_52,A_50,B_51)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1623,plain,(
    ! [B_365,A_366,C_367] :
      ( B_365 = '#skF_6'
      | k1_relset_1(A_366,B_365,C_367) = A_366
      | ~ v1_funct_2(C_367,A_366,B_365)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(A_366,B_365))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_68])).

tff(c_1629,plain,(
    ! [B_368,A_369] :
      ( B_368 = '#skF_6'
      | k1_relset_1(A_369,B_368,'#skF_6') = A_369
      | ~ v1_funct_2('#skF_6',A_369,B_368) ) ),
    inference(resolution,[status(thm)],[c_1036,c_1623])).

tff(c_1641,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1629])).

tff(c_1648,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1038,c_1641])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1037,plain,(
    ! [A_6] : r1_tarski('#skF_6',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_8])).

tff(c_1818,plain,(
    ! [D_394,A_395,B_396,C_397] :
      ( r2_hidden(k4_tarski(D_394,'#skF_3'(A_395,B_396,C_397,D_394)),C_397)
      | ~ r2_hidden(D_394,B_396)
      | k1_relset_1(B_396,A_395,C_397) != B_396
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(B_396,A_395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1963,plain,(
    ! [C_416,D_417,A_418,B_419] :
      ( ~ r1_tarski(C_416,k4_tarski(D_417,'#skF_3'(A_418,B_419,C_416,D_417)))
      | ~ r2_hidden(D_417,B_419)
      | k1_relset_1(B_419,A_418,C_416) != B_419
      | ~ m1_subset_1(C_416,k1_zfmisc_1(k2_zfmisc_1(B_419,A_418))) ) ),
    inference(resolution,[status(thm)],[c_1818,c_42])).

tff(c_1975,plain,(
    ! [D_417,B_419,A_418] :
      ( ~ r2_hidden(D_417,B_419)
      | k1_relset_1(B_419,A_418,'#skF_6') != B_419
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_419,A_418))) ) ),
    inference(resolution,[status(thm)],[c_1037,c_1963])).

tff(c_1981,plain,(
    ! [D_420,B_421,A_422] :
      ( ~ r2_hidden(D_420,B_421)
      | k1_relset_1(B_421,A_422,'#skF_6') != B_421 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_1975])).

tff(c_2003,plain,(
    ! [A_423,A_424,B_425] :
      ( k1_relset_1(A_423,A_424,'#skF_6') != A_423
      | r1_tarski(A_423,B_425) ) ),
    inference(resolution,[status(thm)],[c_6,c_1981])).

tff(c_2014,plain,(
    ! [B_426] : r1_tarski(k1_tarski('#skF_4'),B_426) ),
    inference(superposition,[status(thm),theory(equality)],[c_1648,c_2003])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1035,plain,(
    ! [A_7] :
      ( A_7 = '#skF_6'
      | ~ r1_tarski(A_7,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_1028,c_10])).

tff(c_2066,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2014,c_1035])).

tff(c_2095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1293,c_2066])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.71  
% 4.10/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.10/1.72  
% 4.10/1.72  %Foreground sorts:
% 4.10/1.72  
% 4.10/1.72  
% 4.10/1.72  %Background operators:
% 4.10/1.72  
% 4.10/1.72  
% 4.10/1.72  %Foreground operators:
% 4.10/1.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.10/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.10/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.10/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.10/1.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.10/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.10/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.10/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.10/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.10/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.10/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.10/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.10/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.10/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.10/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.10/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.10/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.10/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.10/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.10/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.10/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.10/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.10/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.10/1.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.10/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.10/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.10/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.10/1.72  
% 4.10/1.73  tff(f_150, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 4.10/1.73  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.10/1.73  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.10/1.73  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.10/1.73  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.10/1.73  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.10/1.73  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.10/1.73  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.10/1.73  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 4.10/1.73  tff(f_61, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.10/1.73  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.10/1.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.10/1.73  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.10/1.73  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 4.10/1.73  tff(f_94, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.10/1.73  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.10/1.73  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.10/1.73  tff(c_137, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.10/1.73  tff(c_145, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_137])).
% 4.10/1.73  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.10/1.73  tff(c_38, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.10/1.73  tff(c_154, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_145, c_38])).
% 4.10/1.73  tff(c_166, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_154])).
% 4.10/1.73  tff(c_309, plain, (![B_112, A_113]: (k1_tarski(k1_funct_1(B_112, A_113))=k2_relat_1(B_112) | k1_tarski(A_113)!=k1_relat_1(B_112) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.10/1.73  tff(c_287, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.10/1.73  tff(c_295, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_287])).
% 4.10/1.73  tff(c_70, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.10/1.73  tff(c_304, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_70])).
% 4.10/1.73  tff(c_315, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_309, c_304])).
% 4.10/1.73  tff(c_328, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_78, c_315])).
% 4.10/1.73  tff(c_236, plain, (![C_97, A_98, B_99]: (v4_relat_1(C_97, A_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.10/1.73  tff(c_244, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_74, c_236])).
% 4.10/1.73  tff(c_34, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(B_22), A_21) | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.10/1.73  tff(c_12, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.10/1.73  tff(c_546, plain, (![B_151, C_152, A_153]: (k2_tarski(B_151, C_152)=A_153 | k1_tarski(C_152)=A_153 | k1_tarski(B_151)=A_153 | k1_xboole_0=A_153 | ~r1_tarski(A_153, k2_tarski(B_151, C_152)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.10/1.73  tff(c_567, plain, (![A_8, A_153]: (k2_tarski(A_8, A_8)=A_153 | k1_tarski(A_8)=A_153 | k1_tarski(A_8)=A_153 | k1_xboole_0=A_153 | ~r1_tarski(A_153, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_546])).
% 4.10/1.73  tff(c_971, plain, (![A_231, A_232]: (k1_tarski(A_231)=A_232 | k1_tarski(A_231)=A_232 | k1_tarski(A_231)=A_232 | k1_xboole_0=A_232 | ~r1_tarski(A_232, k1_tarski(A_231)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_567])).
% 4.10/1.73  tff(c_1009, plain, (![A_236, B_237]: (k1_tarski(A_236)=k1_relat_1(B_237) | k1_relat_1(B_237)=k1_xboole_0 | ~v4_relat_1(B_237, k1_tarski(A_236)) | ~v1_relat_1(B_237))), inference(resolution, [status(thm)], [c_34, c_971])).
% 4.10/1.73  tff(c_1019, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_244, c_1009])).
% 4.10/1.73  tff(c_1025, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_145, c_1019])).
% 4.10/1.73  tff(c_1027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_328, c_1025])).
% 4.10/1.73  tff(c_1028, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_154])).
% 4.10/1.73  tff(c_1029, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_154])).
% 4.10/1.73  tff(c_1044, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_1029])).
% 4.10/1.73  tff(c_1274, plain, (![B_289, A_290]: (k1_tarski(k1_funct_1(B_289, A_290))=k2_relat_1(B_289) | k1_tarski(A_290)!=k1_relat_1(B_289) | ~v1_funct_1(B_289) | ~v1_relat_1(B_289))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.10/1.73  tff(c_28, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.10/1.73  tff(c_1036, plain, (![A_17]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_28])).
% 4.10/1.73  tff(c_1231, plain, (![A_282, B_283, C_284]: (k2_relset_1(A_282, B_283, C_284)=k2_relat_1(C_284) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.10/1.73  tff(c_1236, plain, (![A_282, B_283]: (k2_relset_1(A_282, B_283, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1036, c_1231])).
% 4.10/1.73  tff(c_1237, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1236, c_70])).
% 4.10/1.73  tff(c_1280, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1274, c_1237])).
% 4.10/1.73  tff(c_1293, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_78, c_1044, c_1280])).
% 4.10/1.73  tff(c_72, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.10/1.73  tff(c_1038, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_72])).
% 4.10/1.73  tff(c_76, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.10/1.73  tff(c_68, plain, (![B_51, A_50, C_52]: (k1_xboole_0=B_51 | k1_relset_1(A_50, B_51, C_52)=A_50 | ~v1_funct_2(C_52, A_50, B_51) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.10/1.73  tff(c_1623, plain, (![B_365, A_366, C_367]: (B_365='#skF_6' | k1_relset_1(A_366, B_365, C_367)=A_366 | ~v1_funct_2(C_367, A_366, B_365) | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(A_366, B_365))))), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_68])).
% 4.10/1.73  tff(c_1629, plain, (![B_368, A_369]: (B_368='#skF_6' | k1_relset_1(A_369, B_368, '#skF_6')=A_369 | ~v1_funct_2('#skF_6', A_369, B_368))), inference(resolution, [status(thm)], [c_1036, c_1623])).
% 4.10/1.73  tff(c_1641, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1629])).
% 4.10/1.73  tff(c_1648, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1038, c_1641])).
% 4.10/1.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.10/1.73  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.10/1.73  tff(c_1037, plain, (![A_6]: (r1_tarski('#skF_6', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_8])).
% 4.10/1.73  tff(c_1818, plain, (![D_394, A_395, B_396, C_397]: (r2_hidden(k4_tarski(D_394, '#skF_3'(A_395, B_396, C_397, D_394)), C_397) | ~r2_hidden(D_394, B_396) | k1_relset_1(B_396, A_395, C_397)!=B_396 | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(B_396, A_395))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.10/1.73  tff(c_42, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.10/1.73  tff(c_1963, plain, (![C_416, D_417, A_418, B_419]: (~r1_tarski(C_416, k4_tarski(D_417, '#skF_3'(A_418, B_419, C_416, D_417))) | ~r2_hidden(D_417, B_419) | k1_relset_1(B_419, A_418, C_416)!=B_419 | ~m1_subset_1(C_416, k1_zfmisc_1(k2_zfmisc_1(B_419, A_418))))), inference(resolution, [status(thm)], [c_1818, c_42])).
% 4.10/1.73  tff(c_1975, plain, (![D_417, B_419, A_418]: (~r2_hidden(D_417, B_419) | k1_relset_1(B_419, A_418, '#skF_6')!=B_419 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_419, A_418))))), inference(resolution, [status(thm)], [c_1037, c_1963])).
% 4.10/1.73  tff(c_1981, plain, (![D_420, B_421, A_422]: (~r2_hidden(D_420, B_421) | k1_relset_1(B_421, A_422, '#skF_6')!=B_421)), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_1975])).
% 4.10/1.73  tff(c_2003, plain, (![A_423, A_424, B_425]: (k1_relset_1(A_423, A_424, '#skF_6')!=A_423 | r1_tarski(A_423, B_425))), inference(resolution, [status(thm)], [c_6, c_1981])).
% 4.10/1.73  tff(c_2014, plain, (![B_426]: (r1_tarski(k1_tarski('#skF_4'), B_426))), inference(superposition, [status(thm), theory('equality')], [c_1648, c_2003])).
% 4.10/1.73  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.10/1.73  tff(c_1035, plain, (![A_7]: (A_7='#skF_6' | ~r1_tarski(A_7, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_1028, c_10])).
% 4.10/1.73  tff(c_2066, plain, (k1_tarski('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_2014, c_1035])).
% 4.10/1.73  tff(c_2095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1293, c_2066])).
% 4.10/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.73  
% 4.10/1.73  Inference rules
% 4.10/1.73  ----------------------
% 4.10/1.73  #Ref     : 0
% 4.10/1.73  #Sup     : 418
% 4.10/1.73  #Fact    : 0
% 4.10/1.73  #Define  : 0
% 4.10/1.73  #Split   : 2
% 4.10/1.73  #Chain   : 0
% 4.10/1.73  #Close   : 0
% 4.10/1.73  
% 4.10/1.73  Ordering : KBO
% 4.10/1.73  
% 4.10/1.73  Simplification rules
% 4.10/1.73  ----------------------
% 4.10/1.73  #Subsume      : 73
% 4.10/1.73  #Demod        : 193
% 4.10/1.73  #Tautology    : 159
% 4.10/1.73  #SimpNegUnit  : 9
% 4.10/1.73  #BackRed      : 13
% 4.10/1.73  
% 4.10/1.73  #Partial instantiations: 0
% 4.10/1.73  #Strategies tried      : 1
% 4.10/1.73  
% 4.10/1.73  Timing (in seconds)
% 4.10/1.73  ----------------------
% 4.10/1.74  Preprocessing        : 0.34
% 4.10/1.74  Parsing              : 0.17
% 4.10/1.74  CNF conversion       : 0.03
% 4.10/1.74  Main loop            : 0.60
% 4.10/1.74  Inferencing          : 0.22
% 4.10/1.74  Reduction            : 0.17
% 4.10/1.74  Demodulation         : 0.12
% 4.10/1.74  BG Simplification    : 0.03
% 4.10/1.74  Subsumption          : 0.13
% 4.10/1.74  Abstraction          : 0.02
% 4.10/1.74  MUC search           : 0.00
% 4.10/1.74  Cooper               : 0.00
% 4.10/1.74  Total                : 0.97
% 4.10/1.74  Index Insertion      : 0.00
% 4.10/1.74  Index Deletion       : 0.00
% 4.10/1.74  Index Matching       : 0.00
% 4.10/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
