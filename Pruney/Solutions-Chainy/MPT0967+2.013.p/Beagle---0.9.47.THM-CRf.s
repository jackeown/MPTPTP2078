%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:14 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :  220 (1442 expanded)
%              Number of leaves         :   35 ( 484 expanded)
%              Depth                    :   16
%              Number of atoms          :  469 (4690 expanded)
%              Number of equality atoms :  120 (1288 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3514,plain,(
    ! [C_397,A_398,B_399] :
      ( v1_relat_1(C_397)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3518,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_3514])).

tff(c_3591,plain,(
    ! [C_415,B_416,A_417] :
      ( v5_relat_1(C_415,B_416)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_417,B_416))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3595,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_3591])).

tff(c_3558,plain,(
    ! [B_409,A_410] :
      ( r1_tarski(k2_relat_1(B_409),A_410)
      | ~ v5_relat_1(B_409,A_410)
      | ~ v1_relat_1(B_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3519,plain,(
    ! [A_400,C_401,B_402] :
      ( r1_tarski(A_400,C_401)
      | ~ r1_tarski(B_402,C_401)
      | ~ r1_tarski(A_400,B_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3528,plain,(
    ! [A_400] :
      ( r1_tarski(A_400,'#skF_4')
      | ~ r1_tarski(A_400,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_3519])).

tff(c_3574,plain,(
    ! [B_409] :
      ( r1_tarski(k2_relat_1(B_409),'#skF_4')
      | ~ v5_relat_1(B_409,'#skF_3')
      | ~ v1_relat_1(B_409) ) ),
    inference(resolution,[status(thm)],[c_3558,c_3528])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3641,plain,(
    ! [A_425,B_426,C_427] :
      ( k1_relset_1(A_425,B_426,C_427) = k1_relat_1(C_427)
      | ~ m1_subset_1(C_427,k1_zfmisc_1(k2_zfmisc_1(A_425,B_426))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3645,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_3641])).

tff(c_3930,plain,(
    ! [B_468,A_469,C_470] :
      ( k1_xboole_0 = B_468
      | k1_relset_1(A_469,B_468,C_470) = A_469
      | ~ v1_funct_2(C_470,A_469,B_468)
      | ~ m1_subset_1(C_470,k1_zfmisc_1(k2_zfmisc_1(A_469,B_468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3936,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_3930])).

tff(c_3940,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3645,c_3936])).

tff(c_3941,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3940])).

tff(c_3757,plain,(
    ! [C_449,A_450,B_451] :
      ( m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_450,B_451)))
      | ~ r1_tarski(k2_relat_1(C_449),B_451)
      | ~ r1_tarski(k1_relat_1(C_449),A_450)
      | ~ v1_relat_1(C_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_71,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_71])).

tff(c_174,plain,(
    ! [C_54,B_55,A_56] :
      ( v5_relat_1(C_54,B_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_178,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_174])).

tff(c_225,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_229,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_225])).

tff(c_2544,plain,(
    ! [B_289,A_290,C_291] :
      ( k1_xboole_0 = B_289
      | k1_relset_1(A_290,B_289,C_291) = A_290
      | ~ v1_funct_2(C_291,A_290,B_289)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_290,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2550,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2544])).

tff(c_2554,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_229,c_2550])).

tff(c_2555,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2554])).

tff(c_142,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(k2_relat_1(B_49),A_50)
      | ~ v5_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_117,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,'#skF_4')
      | ~ r1_tarski(A_43,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_108])).

tff(c_158,plain,(
    ! [B_49] :
      ( r1_tarski(k2_relat_1(B_49),'#skF_4')
      | ~ v5_relat_1(B_49,'#skF_3')
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_142,c_117])).

tff(c_2008,plain,(
    ! [C_238,A_239,B_240] :
      ( m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240)))
      | ~ r1_tarski(k2_relat_1(C_238),B_240)
      | ~ r1_tarski(k1_relat_1(C_238),A_239)
      | ~ v1_relat_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2515,plain,(
    ! [A_284,B_285,C_286] :
      ( k1_relset_1(A_284,B_285,C_286) = k1_relat_1(C_286)
      | ~ r1_tarski(k2_relat_1(C_286),B_285)
      | ~ r1_tarski(k1_relat_1(C_286),A_284)
      | ~ v1_relat_1(C_286) ) ),
    inference(resolution,[status(thm)],[c_2008,c_24])).

tff(c_2593,plain,(
    ! [A_293,B_294] :
      ( k1_relset_1(A_293,'#skF_4',B_294) = k1_relat_1(B_294)
      | ~ r1_tarski(k1_relat_1(B_294),A_293)
      | ~ v5_relat_1(B_294,'#skF_3')
      | ~ v1_relat_1(B_294) ) ),
    inference(resolution,[status(thm)],[c_158,c_2515])).

tff(c_2596,plain,(
    ! [A_293] :
      ( k1_relset_1(A_293,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_293)
      | ~ v5_relat_1('#skF_5','#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2555,c_2593])).

tff(c_2604,plain,(
    ! [A_295] :
      ( k1_relset_1(A_295,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_178,c_2555,c_2596])).

tff(c_2609,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_2604])).

tff(c_575,plain,(
    ! [B_121,A_122,C_123] :
      ( k1_xboole_0 = B_121
      | k1_relset_1(A_122,B_121,C_123) = A_122
      | ~ v1_funct_2(C_123,A_122,B_121)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_581,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_575])).

tff(c_585,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_229,c_581])).

tff(c_586,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_585])).

tff(c_439,plain,(
    ! [C_95,A_96,B_97] :
      ( m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ r1_tarski(k2_relat_1(C_95),B_97)
      | ~ r1_tarski(k1_relat_1(C_95),A_96)
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_551,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ r1_tarski(k2_relat_1(C_120),B_119)
      | ~ r1_tarski(k1_relat_1(C_120),A_118)
      | ~ v1_relat_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_439,c_24])).

tff(c_620,plain,(
    ! [A_125,B_126] :
      ( k1_relset_1(A_125,'#skF_4',B_126) = k1_relat_1(B_126)
      | ~ r1_tarski(k1_relat_1(B_126),A_125)
      | ~ v5_relat_1(B_126,'#skF_3')
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_158,c_551])).

tff(c_623,plain,(
    ! [A_125] :
      ( k1_relset_1(A_125,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_125)
      | ~ v5_relat_1('#skF_5','#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_620])).

tff(c_631,plain,(
    ! [A_127] :
      ( k1_relset_1(A_127,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_178,c_586,c_623])).

tff(c_636,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_631])).

tff(c_180,plain,(
    ! [B_58] :
      ( r1_tarski(k2_relat_1(B_58),'#skF_4')
      | ~ v5_relat_1(B_58,'#skF_3')
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_142,c_117])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( v5_relat_1(B_8,A_7)
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_191,plain,(
    ! [B_59] :
      ( v5_relat_1(B_59,'#skF_4')
      | ~ v5_relat_1(B_59,'#skF_3')
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_180,c_12])).

tff(c_194,plain,
    ( v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_178,c_191])).

tff(c_197,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_194])).

tff(c_164,plain,(
    ! [B_52,A_53] :
      ( v5_relat_1(B_52,A_53)
      | ~ r1_tarski(k2_relat_1(B_52),A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_173,plain,(
    ! [B_52] :
      ( v5_relat_1(B_52,k2_relat_1(B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_164])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_257,plain,(
    ! [A_72,A_73,B_74] :
      ( r1_tarski(A_72,A_73)
      | ~ r1_tarski(A_72,k2_relat_1(B_74))
      | ~ v5_relat_1(B_74,A_73)
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_142,c_8])).

tff(c_341,plain,(
    ! [B_89,A_90,B_91] :
      ( r1_tarski(k2_relat_1(B_89),A_90)
      | ~ v5_relat_1(B_91,A_90)
      | ~ v1_relat_1(B_91)
      | ~ v5_relat_1(B_89,k2_relat_1(B_91))
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_14,c_257])).

tff(c_347,plain,(
    ! [B_89] :
      ( r1_tarski(k2_relat_1(B_89),'#skF_3')
      | ~ v1_relat_1('#skF_5')
      | ~ v5_relat_1(B_89,k2_relat_1('#skF_5'))
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_178,c_341])).

tff(c_355,plain,(
    ! [B_92] :
      ( r1_tarski(k2_relat_1(B_92),'#skF_3')
      | ~ v5_relat_1(B_92,k2_relat_1('#skF_5'))
      | ~ v1_relat_1(B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_347])).

tff(c_359,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_173,c_355])).

tff(c_362,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_359])).

tff(c_376,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_362,c_117])).

tff(c_26,plain,(
    ! [C_22,A_20,B_21] :
      ( m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ r1_tarski(k2_relat_1(C_22),B_21)
      | ~ r1_tarski(k1_relat_1(C_22),A_20)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_530,plain,(
    ! [B_110,C_111,A_112] :
      ( k1_xboole_0 = B_110
      | v1_funct_2(C_111,A_112,B_110)
      | k1_relset_1(A_112,B_110,C_111) != A_112
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1100,plain,(
    ! [B_184,C_185,A_186] :
      ( k1_xboole_0 = B_184
      | v1_funct_2(C_185,A_186,B_184)
      | k1_relset_1(A_186,B_184,C_185) != A_186
      | ~ r1_tarski(k2_relat_1(C_185),B_184)
      | ~ r1_tarski(k1_relat_1(C_185),A_186)
      | ~ v1_relat_1(C_185) ) ),
    inference(resolution,[status(thm)],[c_26,c_530])).

tff(c_1102,plain,(
    ! [A_186] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_186,'#skF_4')
      | k1_relset_1(A_186,'#skF_4','#skF_5') != A_186
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_186)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_376,c_1100])).

tff(c_1116,plain,(
    ! [A_186] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_186,'#skF_4')
      | k1_relset_1(A_186,'#skF_4','#skF_5') != A_186
      | ~ r1_tarski('#skF_2',A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_586,c_1102])).

tff(c_1138,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1116])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_116,plain,(
    ! [A_43,A_6] :
      ( r1_tarski(A_43,A_6)
      | ~ r1_tarski(A_43,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_108])).

tff(c_159,plain,(
    ! [B_49,A_6] :
      ( r1_tarski(k2_relat_1(B_49),A_6)
      | ~ v5_relat_1(B_49,k1_xboole_0)
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_142,c_116])).

tff(c_881,plain,(
    ! [A_157,A_158,B_159] :
      ( k1_relset_1(A_157,A_158,B_159) = k1_relat_1(B_159)
      | ~ r1_tarski(k1_relat_1(B_159),A_157)
      | ~ v5_relat_1(B_159,k1_xboole_0)
      | ~ v1_relat_1(B_159) ) ),
    inference(resolution,[status(thm)],[c_159,c_551])).

tff(c_883,plain,(
    ! [A_157,A_158] :
      ( k1_relset_1(A_157,A_158,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_157)
      | ~ v5_relat_1('#skF_5',k1_xboole_0)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_881])).

tff(c_888,plain,(
    ! [A_157,A_158] :
      ( k1_relset_1(A_157,A_158,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_157)
      | ~ v5_relat_1('#skF_5',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_586,c_883])).

tff(c_890,plain,(
    ~ v5_relat_1('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_888])).

tff(c_1152,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_890])).

tff(c_1175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_1152])).

tff(c_1184,plain,(
    ! [A_189] :
      ( v1_funct_2('#skF_5',A_189,'#skF_4')
      | k1_relset_1(A_189,'#skF_4','#skF_5') != A_189
      | ~ r1_tarski('#skF_2',A_189) ) ),
    inference(splitRight,[status(thm)],[c_1116])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52])).

tff(c_70,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1193,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1184,c_70])).

tff(c_1203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_636,c_1193])).

tff(c_1205,plain,(
    v5_relat_1('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_198,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k2_relat_1(B_60),A_61)
      | ~ v5_relat_1(B_60,k1_xboole_0)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_142,c_116])).

tff(c_217,plain,(
    ! [B_60,A_61] :
      ( v5_relat_1(B_60,A_61)
      | ~ v5_relat_1(B_60,k1_xboole_0)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_198,c_12])).

tff(c_1214,plain,(
    ! [A_61] :
      ( v5_relat_1('#skF_5',A_61)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1205,c_217])).

tff(c_1227,plain,(
    ! [A_61] : v5_relat_1('#skF_5',A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1214])).

tff(c_798,plain,(
    ! [A_146,A_147,B_148] :
      ( k1_relset_1(A_146,A_147,B_148) = k1_relat_1(B_148)
      | ~ r1_tarski(k1_relat_1(B_148),A_146)
      | ~ v5_relat_1(B_148,A_147)
      | ~ v1_relat_1(B_148) ) ),
    inference(resolution,[status(thm)],[c_14,c_551])).

tff(c_800,plain,(
    ! [A_146,A_147] :
      ( k1_relset_1(A_146,A_147,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_146)
      | ~ v5_relat_1('#skF_5',A_147)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_798])).

tff(c_813,plain,(
    ! [A_151,A_152] :
      ( k1_relset_1(A_151,A_152,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_151)
      | ~ v5_relat_1('#skF_5',A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_586,c_800])).

tff(c_817,plain,(
    ! [A_152] :
      ( k1_relset_1('#skF_2',A_152,'#skF_5') = '#skF_2'
      | ~ v5_relat_1('#skF_5',A_152) ) ),
    inference(resolution,[status(thm)],[c_6,c_813])).

tff(c_1233,plain,(
    ! [A_152] : k1_relset_1('#skF_2',A_152,'#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1227,c_817])).

tff(c_76,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_161,plain,(
    ! [B_49] :
      ( k2_relat_1(B_49) = k1_xboole_0
      | ~ v5_relat_1(B_49,k1_xboole_0)
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_142,c_87])).

tff(c_1217,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1205,c_161])).

tff(c_1230,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1217])).

tff(c_1715,plain,(
    ! [B_228,C_229,A_230] :
      ( k1_xboole_0 = B_228
      | v1_funct_2(C_229,A_230,B_228)
      | k1_relset_1(A_230,B_228,C_229) != A_230
      | ~ r1_tarski(k2_relat_1(C_229),B_228)
      | ~ r1_tarski(k1_relat_1(C_229),A_230)
      | ~ v1_relat_1(C_229) ) ),
    inference(resolution,[status(thm)],[c_26,c_530])).

tff(c_1717,plain,(
    ! [B_228,A_230] :
      ( k1_xboole_0 = B_228
      | v1_funct_2('#skF_5',A_230,B_228)
      | k1_relset_1(A_230,B_228,'#skF_5') != A_230
      | ~ r1_tarski(k1_xboole_0,B_228)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_230)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_1715])).

tff(c_1733,plain,(
    ! [B_231,A_232] :
      ( k1_xboole_0 = B_231
      | v1_funct_2('#skF_5',A_232,B_231)
      | k1_relset_1(A_232,B_231,'#skF_5') != A_232
      | ~ r1_tarski('#skF_2',A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_586,c_10,c_1717])).

tff(c_1759,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1733,c_70])).

tff(c_1785,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1233,c_1759])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_390,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_376,c_2])).

tff(c_438,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_1309,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1230,c_438])).

tff(c_1806,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1785,c_1309])).

tff(c_1832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1806])).

tff(c_1833,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_378,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_362,c_2])).

tff(c_414,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_1873,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1833,c_414])).

tff(c_1880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1873])).

tff(c_1881,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_2370,plain,(
    ! [B_271,C_272,A_273] :
      ( k1_xboole_0 = B_271
      | v1_funct_2(C_272,A_273,B_271)
      | k1_relset_1(A_273,B_271,C_272) != A_273
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_273,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3376,plain,(
    ! [B_389,C_390,A_391] :
      ( k1_xboole_0 = B_389
      | v1_funct_2(C_390,A_391,B_389)
      | k1_relset_1(A_391,B_389,C_390) != A_391
      | ~ r1_tarski(k2_relat_1(C_390),B_389)
      | ~ r1_tarski(k1_relat_1(C_390),A_391)
      | ~ v1_relat_1(C_390) ) ),
    inference(resolution,[status(thm)],[c_26,c_2370])).

tff(c_3382,plain,(
    ! [B_389,A_391] :
      ( k1_xboole_0 = B_389
      | v1_funct_2('#skF_5',A_391,B_389)
      | k1_relset_1(A_391,B_389,'#skF_5') != A_391
      | ~ r1_tarski('#skF_3',B_389)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_391)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1881,c_3376])).

tff(c_3400,plain,(
    ! [B_392,A_393] :
      ( k1_xboole_0 = B_392
      | v1_funct_2('#skF_5',A_393,B_392)
      | k1_relset_1(A_393,B_392,'#skF_5') != A_393
      | ~ r1_tarski('#skF_3',B_392)
      | ~ r1_tarski('#skF_2',A_393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_2555,c_3382])).

tff(c_3420,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_3400,c_70])).

tff(c_3439,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56,c_2609,c_3420])).

tff(c_1917,plain,(
    ! [A_7] :
      ( v5_relat_1('#skF_5',A_7)
      | ~ r1_tarski('#skF_3',A_7)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1881,c_12])).

tff(c_1967,plain,(
    ! [A_237] :
      ( v5_relat_1('#skF_5',A_237)
      | ~ r1_tarski('#skF_3',A_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1917])).

tff(c_1989,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1967,c_161])).

tff(c_2006,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1881,c_1989])).

tff(c_2007,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2006])).

tff(c_3466,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3439,c_2007])).

tff(c_3484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3466])).

tff(c_3485,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3788,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3757,c_3485])).

tff(c_3799,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3518,c_3788])).

tff(c_3800,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3799])).

tff(c_3942,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3941,c_3800])).

tff(c_3946,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3942])).

tff(c_3947,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3799])).

tff(c_3954,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3574,c_3947])).

tff(c_3964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3518,c_3595,c_3954])).

tff(c_3966,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3965,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3972,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3966,c_3965])).

tff(c_3977,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_58])).

tff(c_4010,plain,(
    ! [C_477,A_478,B_479] :
      ( v1_relat_1(C_477)
      | ~ m1_subset_1(C_477,k1_zfmisc_1(k2_zfmisc_1(A_478,B_479))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4014,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3977,c_4010])).

tff(c_3967,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3965,c_10])).

tff(c_3983,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_3967])).

tff(c_3978,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_60])).

tff(c_4512,plain,(
    ! [A_560,B_561,C_562] :
      ( k1_relset_1(A_560,B_561,C_562) = k1_relat_1(C_562)
      | ~ m1_subset_1(C_562,k1_zfmisc_1(k2_zfmisc_1(A_560,B_561))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4516,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3977,c_4512])).

tff(c_36,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4643,plain,(
    ! [B_579,C_580] :
      ( k1_relset_1('#skF_3',B_579,C_580) = '#skF_3'
      | ~ v1_funct_2(C_580,'#skF_3',B_579)
      | ~ m1_subset_1(C_580,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_579))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3966,c_3966,c_3966,c_3966,c_36])).

tff(c_4646,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_3977,c_4643])).

tff(c_4649,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3978,c_4516,c_4646])).

tff(c_4423,plain,(
    ! [C_545,B_546,A_547] :
      ( v5_relat_1(C_545,B_546)
      | ~ m1_subset_1(C_545,k1_zfmisc_1(k2_zfmisc_1(A_547,B_546))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4427,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_3977,c_4423])).

tff(c_4406,plain,(
    ! [B_542,A_543] :
      ( r1_tarski(k2_relat_1(B_542),A_543)
      | ~ v5_relat_1(B_542,A_543)
      | ~ v1_relat_1(B_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3987,plain,(
    ! [B_474,A_475] :
      ( B_474 = A_475
      | ~ r1_tarski(B_474,A_475)
      | ~ r1_tarski(A_475,B_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3992,plain,(
    ! [A_6] :
      ( A_6 = '#skF_3'
      | ~ r1_tarski(A_6,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3983,c_3987])).

tff(c_4420,plain,(
    ! [B_542] :
      ( k2_relat_1(B_542) = '#skF_3'
      | ~ v5_relat_1(B_542,'#skF_3')
      | ~ v1_relat_1(B_542) ) ),
    inference(resolution,[status(thm)],[c_4406,c_3992])).

tff(c_4430,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4427,c_4420])).

tff(c_4433,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_4430])).

tff(c_4668,plain,(
    ! [C_584,A_585,B_586] :
      ( m1_subset_1(C_584,k1_zfmisc_1(k2_zfmisc_1(A_585,B_586)))
      | ~ r1_tarski(k2_relat_1(C_584),B_586)
      | ~ r1_tarski(k1_relat_1(C_584),A_585)
      | ~ v1_relat_1(C_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4132,plain,(
    ! [A_500,B_501,C_502] :
      ( k1_relset_1(A_500,B_501,C_502) = k1_relat_1(C_502)
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(A_500,B_501))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4136,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3977,c_4132])).

tff(c_4265,plain,(
    ! [B_520,C_521] :
      ( k1_relset_1('#skF_3',B_520,C_521) = '#skF_3'
      | ~ v1_funct_2(C_521,'#skF_3',B_520)
      | ~ m1_subset_1(C_521,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_520))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3966,c_3966,c_3966,c_3966,c_36])).

tff(c_4268,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_3977,c_4265])).

tff(c_4271,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3978,c_4136,c_4268])).

tff(c_4359,plain,(
    ! [C_534,B_535] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_534),B_535,C_534),k1_relat_1(C_534))
      | v1_funct_2(C_534,k1_relat_1(C_534),B_535)
      | ~ v1_funct_1(C_534)
      | ~ v1_relat_1(C_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4365,plain,(
    ! [B_535] :
      ( r2_hidden('#skF_1'('#skF_3',B_535,'#skF_5'),k1_relat_1('#skF_5'))
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_535)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4271,c_4359])).

tff(c_4374,plain,(
    ! [B_536] :
      ( r2_hidden('#skF_1'('#skF_3',B_536,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_536) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_62,c_4271,c_4271,c_4365])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4377,plain,(
    ! [B_536] :
      ( ~ r1_tarski('#skF_3','#skF_1'('#skF_3',B_536,'#skF_5'))
      | v1_funct_2('#skF_5','#skF_3',B_536) ) ),
    inference(resolution,[status(thm)],[c_4374,c_16])).

tff(c_4380,plain,(
    ! [B_536] : v1_funct_2('#skF_5','#skF_3',B_536) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3983,c_4377])).

tff(c_4015,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_3972,c_64])).

tff(c_4016,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4015])).

tff(c_4385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4380,c_4016])).

tff(c_4386,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_4015])).

tff(c_4696,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4668,c_4386])).

tff(c_4710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_3983,c_4649,c_3983,c_4433,c_4696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.10  
% 5.73/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.10  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.73/2.10  
% 5.73/2.10  %Foreground sorts:
% 5.73/2.10  
% 5.73/2.10  
% 5.73/2.10  %Background operators:
% 5.73/2.10  
% 5.73/2.10  
% 5.73/2.10  %Foreground operators:
% 5.73/2.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.73/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.73/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.73/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.73/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.73/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.73/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.73/2.10  tff('#skF_5', type, '#skF_5': $i).
% 5.73/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.73/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.73/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.73/2.10  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.73/2.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.73/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.73/2.10  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.73/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.73/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.73/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.73/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.73/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.73/2.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.73/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.73/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.73/2.10  
% 5.92/2.13  tff(f_127, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 5.92/2.13  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.92/2.13  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.92/2.13  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.92/2.13  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.92/2.13  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.92/2.13  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.92/2.13  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.92/2.13  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.92/2.13  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.92/2.13  tff(f_107, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 5.92/2.13  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.92/2.13  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.92/2.13  tff(c_3514, plain, (![C_397, A_398, B_399]: (v1_relat_1(C_397) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.92/2.13  tff(c_3518, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_3514])).
% 5.92/2.13  tff(c_3591, plain, (![C_415, B_416, A_417]: (v5_relat_1(C_415, B_416) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_417, B_416))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.92/2.13  tff(c_3595, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_3591])).
% 5.92/2.13  tff(c_3558, plain, (![B_409, A_410]: (r1_tarski(k2_relat_1(B_409), A_410) | ~v5_relat_1(B_409, A_410) | ~v1_relat_1(B_409))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.13  tff(c_56, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.92/2.13  tff(c_3519, plain, (![A_400, C_401, B_402]: (r1_tarski(A_400, C_401) | ~r1_tarski(B_402, C_401) | ~r1_tarski(A_400, B_402))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.92/2.13  tff(c_3528, plain, (![A_400]: (r1_tarski(A_400, '#skF_4') | ~r1_tarski(A_400, '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_3519])).
% 5.92/2.13  tff(c_3574, plain, (![B_409]: (r1_tarski(k2_relat_1(B_409), '#skF_4') | ~v5_relat_1(B_409, '#skF_3') | ~v1_relat_1(B_409))), inference(resolution, [status(thm)], [c_3558, c_3528])).
% 5.92/2.13  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.13  tff(c_54, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.92/2.13  tff(c_68, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_54])).
% 5.92/2.13  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.92/2.13  tff(c_3641, plain, (![A_425, B_426, C_427]: (k1_relset_1(A_425, B_426, C_427)=k1_relat_1(C_427) | ~m1_subset_1(C_427, k1_zfmisc_1(k2_zfmisc_1(A_425, B_426))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.13  tff(c_3645, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_3641])).
% 5.92/2.13  tff(c_3930, plain, (![B_468, A_469, C_470]: (k1_xboole_0=B_468 | k1_relset_1(A_469, B_468, C_470)=A_469 | ~v1_funct_2(C_470, A_469, B_468) | ~m1_subset_1(C_470, k1_zfmisc_1(k2_zfmisc_1(A_469, B_468))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.92/2.13  tff(c_3936, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_3930])).
% 5.92/2.13  tff(c_3940, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3645, c_3936])).
% 5.92/2.13  tff(c_3941, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_68, c_3940])).
% 5.92/2.13  tff(c_3757, plain, (![C_449, A_450, B_451]: (m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_450, B_451))) | ~r1_tarski(k2_relat_1(C_449), B_451) | ~r1_tarski(k1_relat_1(C_449), A_450) | ~v1_relat_1(C_449))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.92/2.13  tff(c_71, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.92/2.13  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_71])).
% 5.92/2.13  tff(c_174, plain, (![C_54, B_55, A_56]: (v5_relat_1(C_54, B_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.92/2.13  tff(c_178, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_174])).
% 5.92/2.13  tff(c_225, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.13  tff(c_229, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_225])).
% 5.92/2.13  tff(c_2544, plain, (![B_289, A_290, C_291]: (k1_xboole_0=B_289 | k1_relset_1(A_290, B_289, C_291)=A_290 | ~v1_funct_2(C_291, A_290, B_289) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_290, B_289))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.92/2.13  tff(c_2550, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_2544])).
% 5.92/2.13  tff(c_2554, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_229, c_2550])).
% 5.92/2.13  tff(c_2555, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_68, c_2554])).
% 5.92/2.13  tff(c_142, plain, (![B_49, A_50]: (r1_tarski(k2_relat_1(B_49), A_50) | ~v5_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.13  tff(c_108, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.92/2.13  tff(c_117, plain, (![A_43]: (r1_tarski(A_43, '#skF_4') | ~r1_tarski(A_43, '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_108])).
% 5.92/2.13  tff(c_158, plain, (![B_49]: (r1_tarski(k2_relat_1(B_49), '#skF_4') | ~v5_relat_1(B_49, '#skF_3') | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_142, c_117])).
% 5.92/2.13  tff(c_2008, plain, (![C_238, A_239, B_240]: (m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))) | ~r1_tarski(k2_relat_1(C_238), B_240) | ~r1_tarski(k1_relat_1(C_238), A_239) | ~v1_relat_1(C_238))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.92/2.13  tff(c_24, plain, (![A_17, B_18, C_19]: (k1_relset_1(A_17, B_18, C_19)=k1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.13  tff(c_2515, plain, (![A_284, B_285, C_286]: (k1_relset_1(A_284, B_285, C_286)=k1_relat_1(C_286) | ~r1_tarski(k2_relat_1(C_286), B_285) | ~r1_tarski(k1_relat_1(C_286), A_284) | ~v1_relat_1(C_286))), inference(resolution, [status(thm)], [c_2008, c_24])).
% 5.92/2.13  tff(c_2593, plain, (![A_293, B_294]: (k1_relset_1(A_293, '#skF_4', B_294)=k1_relat_1(B_294) | ~r1_tarski(k1_relat_1(B_294), A_293) | ~v5_relat_1(B_294, '#skF_3') | ~v1_relat_1(B_294))), inference(resolution, [status(thm)], [c_158, c_2515])).
% 5.92/2.13  tff(c_2596, plain, (![A_293]: (k1_relset_1(A_293, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_293) | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2555, c_2593])).
% 5.92/2.13  tff(c_2604, plain, (![A_295]: (k1_relset_1(A_295, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_295))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_178, c_2555, c_2596])).
% 5.92/2.13  tff(c_2609, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_6, c_2604])).
% 5.92/2.13  tff(c_575, plain, (![B_121, A_122, C_123]: (k1_xboole_0=B_121 | k1_relset_1(A_122, B_121, C_123)=A_122 | ~v1_funct_2(C_123, A_122, B_121) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.92/2.13  tff(c_581, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_575])).
% 5.92/2.13  tff(c_585, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_229, c_581])).
% 5.92/2.13  tff(c_586, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_68, c_585])).
% 5.92/2.13  tff(c_439, plain, (![C_95, A_96, B_97]: (m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~r1_tarski(k2_relat_1(C_95), B_97) | ~r1_tarski(k1_relat_1(C_95), A_96) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.92/2.13  tff(c_551, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~r1_tarski(k2_relat_1(C_120), B_119) | ~r1_tarski(k1_relat_1(C_120), A_118) | ~v1_relat_1(C_120))), inference(resolution, [status(thm)], [c_439, c_24])).
% 5.92/2.13  tff(c_620, plain, (![A_125, B_126]: (k1_relset_1(A_125, '#skF_4', B_126)=k1_relat_1(B_126) | ~r1_tarski(k1_relat_1(B_126), A_125) | ~v5_relat_1(B_126, '#skF_3') | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_158, c_551])).
% 5.92/2.13  tff(c_623, plain, (![A_125]: (k1_relset_1(A_125, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_125) | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_586, c_620])).
% 5.92/2.13  tff(c_631, plain, (![A_127]: (k1_relset_1(A_127, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_127))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_178, c_586, c_623])).
% 5.92/2.13  tff(c_636, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_6, c_631])).
% 5.92/2.13  tff(c_180, plain, (![B_58]: (r1_tarski(k2_relat_1(B_58), '#skF_4') | ~v5_relat_1(B_58, '#skF_3') | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_142, c_117])).
% 5.92/2.13  tff(c_12, plain, (![B_8, A_7]: (v5_relat_1(B_8, A_7) | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.13  tff(c_191, plain, (![B_59]: (v5_relat_1(B_59, '#skF_4') | ~v5_relat_1(B_59, '#skF_3') | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_180, c_12])).
% 5.92/2.13  tff(c_194, plain, (v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_178, c_191])).
% 5.92/2.13  tff(c_197, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_194])).
% 5.92/2.13  tff(c_164, plain, (![B_52, A_53]: (v5_relat_1(B_52, A_53) | ~r1_tarski(k2_relat_1(B_52), A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.13  tff(c_173, plain, (![B_52]: (v5_relat_1(B_52, k2_relat_1(B_52)) | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_6, c_164])).
% 5.92/2.13  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.13  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.92/2.13  tff(c_257, plain, (![A_72, A_73, B_74]: (r1_tarski(A_72, A_73) | ~r1_tarski(A_72, k2_relat_1(B_74)) | ~v5_relat_1(B_74, A_73) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_142, c_8])).
% 5.92/2.13  tff(c_341, plain, (![B_89, A_90, B_91]: (r1_tarski(k2_relat_1(B_89), A_90) | ~v5_relat_1(B_91, A_90) | ~v1_relat_1(B_91) | ~v5_relat_1(B_89, k2_relat_1(B_91)) | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_14, c_257])).
% 5.92/2.13  tff(c_347, plain, (![B_89]: (r1_tarski(k2_relat_1(B_89), '#skF_3') | ~v1_relat_1('#skF_5') | ~v5_relat_1(B_89, k2_relat_1('#skF_5')) | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_178, c_341])).
% 5.92/2.13  tff(c_355, plain, (![B_92]: (r1_tarski(k2_relat_1(B_92), '#skF_3') | ~v5_relat_1(B_92, k2_relat_1('#skF_5')) | ~v1_relat_1(B_92))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_347])).
% 5.92/2.13  tff(c_359, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_173, c_355])).
% 5.92/2.13  tff(c_362, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_359])).
% 5.92/2.13  tff(c_376, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_362, c_117])).
% 5.92/2.13  tff(c_26, plain, (![C_22, A_20, B_21]: (m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~r1_tarski(k2_relat_1(C_22), B_21) | ~r1_tarski(k1_relat_1(C_22), A_20) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.92/2.13  tff(c_530, plain, (![B_110, C_111, A_112]: (k1_xboole_0=B_110 | v1_funct_2(C_111, A_112, B_110) | k1_relset_1(A_112, B_110, C_111)!=A_112 | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_110))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.92/2.13  tff(c_1100, plain, (![B_184, C_185, A_186]: (k1_xboole_0=B_184 | v1_funct_2(C_185, A_186, B_184) | k1_relset_1(A_186, B_184, C_185)!=A_186 | ~r1_tarski(k2_relat_1(C_185), B_184) | ~r1_tarski(k1_relat_1(C_185), A_186) | ~v1_relat_1(C_185))), inference(resolution, [status(thm)], [c_26, c_530])).
% 5.92/2.13  tff(c_1102, plain, (![A_186]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_186, '#skF_4') | k1_relset_1(A_186, '#skF_4', '#skF_5')!=A_186 | ~r1_tarski(k1_relat_1('#skF_5'), A_186) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_376, c_1100])).
% 5.92/2.13  tff(c_1116, plain, (![A_186]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_186, '#skF_4') | k1_relset_1(A_186, '#skF_4', '#skF_5')!=A_186 | ~r1_tarski('#skF_2', A_186))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_586, c_1102])).
% 5.92/2.13  tff(c_1138, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1116])).
% 5.92/2.13  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.92/2.13  tff(c_116, plain, (![A_43, A_6]: (r1_tarski(A_43, A_6) | ~r1_tarski(A_43, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_108])).
% 5.92/2.13  tff(c_159, plain, (![B_49, A_6]: (r1_tarski(k2_relat_1(B_49), A_6) | ~v5_relat_1(B_49, k1_xboole_0) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_142, c_116])).
% 5.92/2.13  tff(c_881, plain, (![A_157, A_158, B_159]: (k1_relset_1(A_157, A_158, B_159)=k1_relat_1(B_159) | ~r1_tarski(k1_relat_1(B_159), A_157) | ~v5_relat_1(B_159, k1_xboole_0) | ~v1_relat_1(B_159))), inference(resolution, [status(thm)], [c_159, c_551])).
% 5.92/2.13  tff(c_883, plain, (![A_157, A_158]: (k1_relset_1(A_157, A_158, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_157) | ~v5_relat_1('#skF_5', k1_xboole_0) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_586, c_881])).
% 5.92/2.13  tff(c_888, plain, (![A_157, A_158]: (k1_relset_1(A_157, A_158, '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_157) | ~v5_relat_1('#skF_5', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_586, c_883])).
% 5.92/2.13  tff(c_890, plain, (~v5_relat_1('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_888])).
% 5.92/2.13  tff(c_1152, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1138, c_890])).
% 5.92/2.13  tff(c_1175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_1152])).
% 5.92/2.13  tff(c_1184, plain, (![A_189]: (v1_funct_2('#skF_5', A_189, '#skF_4') | k1_relset_1(A_189, '#skF_4', '#skF_5')!=A_189 | ~r1_tarski('#skF_2', A_189))), inference(splitRight, [status(thm)], [c_1116])).
% 5.92/2.13  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.92/2.13  tff(c_52, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.92/2.13  tff(c_64, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52])).
% 5.92/2.13  tff(c_70, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 5.92/2.13  tff(c_1193, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1184, c_70])).
% 5.92/2.13  tff(c_1203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_636, c_1193])).
% 5.92/2.13  tff(c_1205, plain, (v5_relat_1('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_888])).
% 5.92/2.13  tff(c_198, plain, (![B_60, A_61]: (r1_tarski(k2_relat_1(B_60), A_61) | ~v5_relat_1(B_60, k1_xboole_0) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_142, c_116])).
% 5.92/2.13  tff(c_217, plain, (![B_60, A_61]: (v5_relat_1(B_60, A_61) | ~v5_relat_1(B_60, k1_xboole_0) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_198, c_12])).
% 5.92/2.13  tff(c_1214, plain, (![A_61]: (v5_relat_1('#skF_5', A_61) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1205, c_217])).
% 5.92/2.13  tff(c_1227, plain, (![A_61]: (v5_relat_1('#skF_5', A_61))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1214])).
% 5.92/2.13  tff(c_798, plain, (![A_146, A_147, B_148]: (k1_relset_1(A_146, A_147, B_148)=k1_relat_1(B_148) | ~r1_tarski(k1_relat_1(B_148), A_146) | ~v5_relat_1(B_148, A_147) | ~v1_relat_1(B_148))), inference(resolution, [status(thm)], [c_14, c_551])).
% 5.92/2.13  tff(c_800, plain, (![A_146, A_147]: (k1_relset_1(A_146, A_147, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_146) | ~v5_relat_1('#skF_5', A_147) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_586, c_798])).
% 5.92/2.13  tff(c_813, plain, (![A_151, A_152]: (k1_relset_1(A_151, A_152, '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_151) | ~v5_relat_1('#skF_5', A_152))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_586, c_800])).
% 5.92/2.13  tff(c_817, plain, (![A_152]: (k1_relset_1('#skF_2', A_152, '#skF_5')='#skF_2' | ~v5_relat_1('#skF_5', A_152))), inference(resolution, [status(thm)], [c_6, c_813])).
% 5.92/2.13  tff(c_1233, plain, (![A_152]: (k1_relset_1('#skF_2', A_152, '#skF_5')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1227, c_817])).
% 5.92/2.13  tff(c_76, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.13  tff(c_87, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_76])).
% 5.92/2.13  tff(c_161, plain, (![B_49]: (k2_relat_1(B_49)=k1_xboole_0 | ~v5_relat_1(B_49, k1_xboole_0) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_142, c_87])).
% 5.92/2.13  tff(c_1217, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1205, c_161])).
% 5.92/2.13  tff(c_1230, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1217])).
% 5.92/2.13  tff(c_1715, plain, (![B_228, C_229, A_230]: (k1_xboole_0=B_228 | v1_funct_2(C_229, A_230, B_228) | k1_relset_1(A_230, B_228, C_229)!=A_230 | ~r1_tarski(k2_relat_1(C_229), B_228) | ~r1_tarski(k1_relat_1(C_229), A_230) | ~v1_relat_1(C_229))), inference(resolution, [status(thm)], [c_26, c_530])).
% 5.92/2.13  tff(c_1717, plain, (![B_228, A_230]: (k1_xboole_0=B_228 | v1_funct_2('#skF_5', A_230, B_228) | k1_relset_1(A_230, B_228, '#skF_5')!=A_230 | ~r1_tarski(k1_xboole_0, B_228) | ~r1_tarski(k1_relat_1('#skF_5'), A_230) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1230, c_1715])).
% 5.92/2.13  tff(c_1733, plain, (![B_231, A_232]: (k1_xboole_0=B_231 | v1_funct_2('#skF_5', A_232, B_231) | k1_relset_1(A_232, B_231, '#skF_5')!=A_232 | ~r1_tarski('#skF_2', A_232))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_586, c_10, c_1717])).
% 5.92/2.13  tff(c_1759, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1733, c_70])).
% 5.92/2.13  tff(c_1785, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1233, c_1759])).
% 5.92/2.13  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.13  tff(c_390, plain, (k2_relat_1('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_376, c_2])).
% 5.92/2.13  tff(c_438, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_390])).
% 5.92/2.13  tff(c_1309, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1230, c_438])).
% 5.92/2.13  tff(c_1806, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1785, c_1309])).
% 5.92/2.13  tff(c_1832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1806])).
% 5.92/2.13  tff(c_1833, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_390])).
% 5.92/2.13  tff(c_378, plain, (k2_relat_1('#skF_5')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_362, c_2])).
% 5.92/2.13  tff(c_414, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_378])).
% 5.92/2.13  tff(c_1873, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1833, c_414])).
% 5.92/2.13  tff(c_1880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1873])).
% 5.92/2.13  tff(c_1881, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_378])).
% 5.92/2.13  tff(c_2370, plain, (![B_271, C_272, A_273]: (k1_xboole_0=B_271 | v1_funct_2(C_272, A_273, B_271) | k1_relset_1(A_273, B_271, C_272)!=A_273 | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(A_273, B_271))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.92/2.13  tff(c_3376, plain, (![B_389, C_390, A_391]: (k1_xboole_0=B_389 | v1_funct_2(C_390, A_391, B_389) | k1_relset_1(A_391, B_389, C_390)!=A_391 | ~r1_tarski(k2_relat_1(C_390), B_389) | ~r1_tarski(k1_relat_1(C_390), A_391) | ~v1_relat_1(C_390))), inference(resolution, [status(thm)], [c_26, c_2370])).
% 5.92/2.13  tff(c_3382, plain, (![B_389, A_391]: (k1_xboole_0=B_389 | v1_funct_2('#skF_5', A_391, B_389) | k1_relset_1(A_391, B_389, '#skF_5')!=A_391 | ~r1_tarski('#skF_3', B_389) | ~r1_tarski(k1_relat_1('#skF_5'), A_391) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1881, c_3376])).
% 5.92/2.13  tff(c_3400, plain, (![B_392, A_393]: (k1_xboole_0=B_392 | v1_funct_2('#skF_5', A_393, B_392) | k1_relset_1(A_393, B_392, '#skF_5')!=A_393 | ~r1_tarski('#skF_3', B_392) | ~r1_tarski('#skF_2', A_393))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_2555, c_3382])).
% 5.92/2.13  tff(c_3420, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_3400, c_70])).
% 5.92/2.13  tff(c_3439, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56, c_2609, c_3420])).
% 5.92/2.13  tff(c_1917, plain, (![A_7]: (v5_relat_1('#skF_5', A_7) | ~r1_tarski('#skF_3', A_7) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1881, c_12])).
% 5.92/2.13  tff(c_1967, plain, (![A_237]: (v5_relat_1('#skF_5', A_237) | ~r1_tarski('#skF_3', A_237))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1917])).
% 5.92/2.13  tff(c_1989, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_1967, c_161])).
% 5.92/2.13  tff(c_2006, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1881, c_1989])).
% 5.92/2.13  tff(c_2007, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_68, c_2006])).
% 5.92/2.13  tff(c_3466, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3439, c_2007])).
% 5.92/2.13  tff(c_3484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3466])).
% 5.92/2.13  tff(c_3485, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_64])).
% 5.92/2.13  tff(c_3788, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3757, c_3485])).
% 5.92/2.13  tff(c_3799, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3518, c_3788])).
% 5.92/2.13  tff(c_3800, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3799])).
% 5.92/2.13  tff(c_3942, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3941, c_3800])).
% 5.92/2.13  tff(c_3946, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3942])).
% 5.92/2.13  tff(c_3947, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_3799])).
% 5.92/2.13  tff(c_3954, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3574, c_3947])).
% 5.92/2.13  tff(c_3964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3518, c_3595, c_3954])).
% 5.92/2.13  tff(c_3966, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_54])).
% 5.92/2.13  tff(c_3965, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 5.92/2.13  tff(c_3972, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3966, c_3965])).
% 5.92/2.13  tff(c_3977, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3972, c_58])).
% 5.92/2.13  tff(c_4010, plain, (![C_477, A_478, B_479]: (v1_relat_1(C_477) | ~m1_subset_1(C_477, k1_zfmisc_1(k2_zfmisc_1(A_478, B_479))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.92/2.13  tff(c_4014, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3977, c_4010])).
% 5.92/2.13  tff(c_3967, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_3965, c_10])).
% 5.92/2.13  tff(c_3983, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_3972, c_3967])).
% 5.92/2.13  tff(c_3978, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3972, c_60])).
% 5.92/2.13  tff(c_4512, plain, (![A_560, B_561, C_562]: (k1_relset_1(A_560, B_561, C_562)=k1_relat_1(C_562) | ~m1_subset_1(C_562, k1_zfmisc_1(k2_zfmisc_1(A_560, B_561))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.13  tff(c_4516, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3977, c_4512])).
% 5.92/2.13  tff(c_36, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.92/2.13  tff(c_4643, plain, (![B_579, C_580]: (k1_relset_1('#skF_3', B_579, C_580)='#skF_3' | ~v1_funct_2(C_580, '#skF_3', B_579) | ~m1_subset_1(C_580, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_579))))), inference(demodulation, [status(thm), theory('equality')], [c_3966, c_3966, c_3966, c_3966, c_36])).
% 5.92/2.13  tff(c_4646, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_3977, c_4643])).
% 5.92/2.13  tff(c_4649, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3978, c_4516, c_4646])).
% 5.92/2.13  tff(c_4423, plain, (![C_545, B_546, A_547]: (v5_relat_1(C_545, B_546) | ~m1_subset_1(C_545, k1_zfmisc_1(k2_zfmisc_1(A_547, B_546))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.92/2.13  tff(c_4427, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_3977, c_4423])).
% 5.92/2.13  tff(c_4406, plain, (![B_542, A_543]: (r1_tarski(k2_relat_1(B_542), A_543) | ~v5_relat_1(B_542, A_543) | ~v1_relat_1(B_542))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.13  tff(c_3987, plain, (![B_474, A_475]: (B_474=A_475 | ~r1_tarski(B_474, A_475) | ~r1_tarski(A_475, B_474))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.13  tff(c_3992, plain, (![A_6]: (A_6='#skF_3' | ~r1_tarski(A_6, '#skF_3'))), inference(resolution, [status(thm)], [c_3983, c_3987])).
% 5.92/2.13  tff(c_4420, plain, (![B_542]: (k2_relat_1(B_542)='#skF_3' | ~v5_relat_1(B_542, '#skF_3') | ~v1_relat_1(B_542))), inference(resolution, [status(thm)], [c_4406, c_3992])).
% 5.92/2.13  tff(c_4430, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4427, c_4420])).
% 5.92/2.13  tff(c_4433, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4014, c_4430])).
% 5.92/2.13  tff(c_4668, plain, (![C_584, A_585, B_586]: (m1_subset_1(C_584, k1_zfmisc_1(k2_zfmisc_1(A_585, B_586))) | ~r1_tarski(k2_relat_1(C_584), B_586) | ~r1_tarski(k1_relat_1(C_584), A_585) | ~v1_relat_1(C_584))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.92/2.13  tff(c_4132, plain, (![A_500, B_501, C_502]: (k1_relset_1(A_500, B_501, C_502)=k1_relat_1(C_502) | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(A_500, B_501))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.13  tff(c_4136, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3977, c_4132])).
% 5.92/2.13  tff(c_4265, plain, (![B_520, C_521]: (k1_relset_1('#skF_3', B_520, C_521)='#skF_3' | ~v1_funct_2(C_521, '#skF_3', B_520) | ~m1_subset_1(C_521, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_520))))), inference(demodulation, [status(thm), theory('equality')], [c_3966, c_3966, c_3966, c_3966, c_36])).
% 5.92/2.13  tff(c_4268, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_3977, c_4265])).
% 5.92/2.13  tff(c_4271, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3978, c_4136, c_4268])).
% 5.92/2.13  tff(c_4359, plain, (![C_534, B_535]: (r2_hidden('#skF_1'(k1_relat_1(C_534), B_535, C_534), k1_relat_1(C_534)) | v1_funct_2(C_534, k1_relat_1(C_534), B_535) | ~v1_funct_1(C_534) | ~v1_relat_1(C_534))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.92/2.13  tff(c_4365, plain, (![B_535]: (r2_hidden('#skF_1'('#skF_3', B_535, '#skF_5'), k1_relat_1('#skF_5')) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_535) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4271, c_4359])).
% 5.92/2.13  tff(c_4374, plain, (![B_536]: (r2_hidden('#skF_1'('#skF_3', B_536, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_536))), inference(demodulation, [status(thm), theory('equality')], [c_4014, c_62, c_4271, c_4271, c_4365])).
% 5.92/2.13  tff(c_16, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.92/2.13  tff(c_4377, plain, (![B_536]: (~r1_tarski('#skF_3', '#skF_1'('#skF_3', B_536, '#skF_5')) | v1_funct_2('#skF_5', '#skF_3', B_536))), inference(resolution, [status(thm)], [c_4374, c_16])).
% 5.92/2.13  tff(c_4380, plain, (![B_536]: (v1_funct_2('#skF_5', '#skF_3', B_536))), inference(demodulation, [status(thm), theory('equality')], [c_3983, c_4377])).
% 5.92/2.13  tff(c_4015, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3972, c_3972, c_64])).
% 5.92/2.13  tff(c_4016, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_4015])).
% 5.92/2.13  tff(c_4385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4380, c_4016])).
% 5.92/2.13  tff(c_4386, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_4015])).
% 5.92/2.13  tff(c_4696, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4668, c_4386])).
% 5.92/2.13  tff(c_4710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4014, c_3983, c_4649, c_3983, c_4433, c_4696])).
% 5.92/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.13  
% 5.92/2.13  Inference rules
% 5.92/2.13  ----------------------
% 5.92/2.13  #Ref     : 0
% 5.92/2.13  #Sup     : 899
% 5.92/2.13  #Fact    : 0
% 5.92/2.13  #Define  : 0
% 5.92/2.13  #Split   : 24
% 5.92/2.13  #Chain   : 0
% 5.92/2.13  #Close   : 0
% 5.92/2.13  
% 5.92/2.13  Ordering : KBO
% 5.92/2.13  
% 5.92/2.13  Simplification rules
% 5.92/2.13  ----------------------
% 5.92/2.13  #Subsume      : 288
% 5.92/2.13  #Demod        : 1191
% 5.92/2.13  #Tautology    : 321
% 5.92/2.13  #SimpNegUnit  : 16
% 5.92/2.13  #BackRed      : 183
% 5.92/2.13  
% 5.92/2.13  #Partial instantiations: 0
% 5.92/2.13  #Strategies tried      : 1
% 5.92/2.13  
% 5.92/2.13  Timing (in seconds)
% 5.92/2.13  ----------------------
% 5.92/2.14  Preprocessing        : 0.33
% 5.92/2.14  Parsing              : 0.17
% 5.92/2.14  CNF conversion       : 0.02
% 5.92/2.14  Main loop            : 0.99
% 5.92/2.14  Inferencing          : 0.35
% 5.92/2.14  Reduction            : 0.31
% 5.92/2.14  Demodulation         : 0.21
% 5.92/2.14  BG Simplification    : 0.04
% 5.92/2.14  Subsumption          : 0.22
% 5.92/2.14  Abstraction          : 0.04
% 5.92/2.14  MUC search           : 0.00
% 5.92/2.14  Cooper               : 0.00
% 5.92/2.14  Total                : 1.39
% 5.92/2.14  Index Insertion      : 0.00
% 5.92/2.14  Index Deletion       : 0.00
% 5.92/2.14  Index Matching       : 0.00
% 5.92/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
