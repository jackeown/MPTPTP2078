%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:51 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 8.10s
% Verified   : 
% Statistics : Number of formulae       :  393 (3804 expanded)
%              Number of leaves         :   36 (1174 expanded)
%              Depth                    :   16
%              Number of atoms          :  753 (10192 expanded)
%              Number of equality atoms :  271 (3265 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_26,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5032,plain,(
    ! [B_486,A_487] :
      ( v1_relat_1(B_486)
      | ~ m1_subset_1(B_486,k1_zfmisc_1(A_487))
      | ~ v1_relat_1(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5041,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_5032])).

tff(c_5051,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5041])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_6086,plain,(
    ! [A_595,B_596,C_597] :
      ( k2_relset_1(A_595,B_596,C_597) = k2_relat_1(C_597)
      | ~ m1_subset_1(C_597,k1_zfmisc_1(k2_zfmisc_1(A_595,B_596))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6096,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_6086])).

tff(c_6109,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6096])).

tff(c_40,plain,(
    ! [A_21] :
      ( k1_relat_1(k2_funct_1(A_21)) = k2_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_189,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_195,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_189])).

tff(c_202,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_195])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_420,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_439,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_420])).

tff(c_683,plain,(
    ! [B_129,A_130,C_131] :
      ( k1_xboole_0 = B_129
      | k1_relset_1(A_130,B_129,C_131) = A_130
      | ~ v1_funct_2(C_131,A_130,B_129)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_693,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_683])).

tff(c_708,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_439,c_693])).

tff(c_712,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_708])).

tff(c_38,plain,(
    ! [A_21] :
      ( k2_relat_1(k2_funct_1(A_21)) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    ! [A_20] :
      ( v1_relat_1(k2_funct_1(A_20))
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_142,plain,(
    ! [A_46] :
      ( v1_funct_1(k2_funct_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_136,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_145,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_136])).

tff(c_148,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_145])).

tff(c_160,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_166,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_160])).

tff(c_173,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_166])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_173])).

tff(c_177,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_628,plain,(
    ! [B_126,A_127] :
      ( m1_subset_1(B_126,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_126),A_127)))
      | ~ r1_tarski(k2_relat_1(B_126),A_127)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_909,plain,(
    ! [B_147,A_148] :
      ( r1_tarski(B_147,k2_zfmisc_1(k1_relat_1(B_147),A_148))
      | ~ r1_tarski(k2_relat_1(B_147),A_148)
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_628,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1286,plain,(
    ! [B_174,A_175] :
      ( k2_zfmisc_1(k1_relat_1(B_174),A_175) = B_174
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(B_174),A_175),B_174)
      | ~ r1_tarski(k2_relat_1(B_174),A_175)
      | ~ v1_funct_1(B_174)
      | ~ v1_relat_1(B_174) ) ),
    inference(resolution,[status(thm)],[c_909,c_2])).

tff(c_1296,plain,(
    ! [B_174] :
      ( k2_zfmisc_1(k1_relat_1(B_174),k1_xboole_0) = B_174
      | ~ r1_tarski(k1_xboole_0,B_174)
      | ~ r1_tarski(k2_relat_1(B_174),k1_xboole_0)
      | ~ v1_funct_1(B_174)
      | ~ v1_relat_1(B_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1286])).

tff(c_1306,plain,(
    ! [B_176] :
      ( k1_xboole_0 = B_176
      | ~ r1_tarski(k2_relat_1(B_176),k1_xboole_0)
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12,c_1296])).

tff(c_1321,plain,(
    ! [A_177] :
      ( k2_funct_1(A_177) = k1_xboole_0
      | ~ r1_tarski(k1_relat_1(A_177),k1_xboole_0)
      | ~ v1_funct_1(k2_funct_1(A_177))
      | ~ v1_relat_1(k2_funct_1(A_177))
      | ~ v2_funct_1(A_177)
      | ~ v1_funct_1(A_177)
      | ~ v1_relat_1(A_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1306])).

tff(c_1324,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_1321])).

tff(c_1332,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_68,c_177,c_1324])).

tff(c_1335,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1332])).

tff(c_1338,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1335])).

tff(c_1342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_1338])).

tff(c_1344,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1332])).

tff(c_337,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_344,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_337])).

tff(c_357,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_344])).

tff(c_1466,plain,(
    ! [A_184,A_185] :
      ( m1_subset_1(k2_funct_1(A_184),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_184),A_185)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_184)),A_185)
      | ~ v1_funct_1(k2_funct_1(A_184))
      | ~ v1_relat_1(k2_funct_1(A_184))
      | ~ v2_funct_1(A_184)
      | ~ v1_funct_1(A_184)
      | ~ v1_relat_1(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_628])).

tff(c_1492,plain,(
    ! [A_185] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_185)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_185)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_1466])).

tff(c_1519,plain,(
    ! [A_186] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_186)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_68,c_1344,c_177,c_1492])).

tff(c_176,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_184,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_1561,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1519,c_184])).

tff(c_1565,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1561])).

tff(c_1568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_68,c_6,c_712,c_1565])).

tff(c_1569,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_668,plain,(
    ! [B_128] :
      ( m1_subset_1(B_128,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_128),k1_xboole_0)
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_628])).

tff(c_671,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_668])).

tff(c_679,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_671])).

tff(c_682,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_679])).

tff(c_1572,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1569,c_682])).

tff(c_1603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1572])).

tff(c_1605,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_679])).

tff(c_232,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_232])).

tff(c_1632,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1605,c_244])).

tff(c_1667,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1632,c_8])).

tff(c_1604,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_679])).

tff(c_1736,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1632,c_1604])).

tff(c_1755,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1736,c_18])).

tff(c_1760,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1755,c_2])).

tff(c_1769,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1667,c_1760])).

tff(c_1664,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1632,c_1632,c_12])).

tff(c_1857,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_1769,c_1664])).

tff(c_126,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_126])).

tff(c_239,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_232])).

tff(c_258,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_1785,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_258])).

tff(c_2051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1857,c_1785])).

tff(c_2052,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_2065,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2052,c_70])).

tff(c_2156,plain,(
    ! [A_222,B_223,C_224] :
      ( k1_relset_1(A_222,B_223,C_224) = k1_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2243,plain,(
    ! [C_238] :
      ( k1_relset_1('#skF_1','#skF_2',C_238) = k1_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2052,c_2156])).

tff(c_2255,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2065,c_2243])).

tff(c_2598,plain,(
    ! [B_278,C_279,A_280] :
      ( k1_xboole_0 = B_278
      | v1_funct_2(C_279,A_280,B_278)
      | k1_relset_1(A_280,B_278,C_279) != A_280
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_280,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2604,plain,(
    ! [C_279] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_279,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_279) != '#skF_1'
      | ~ m1_subset_1(C_279,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2052,c_2598])).

tff(c_2672,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2604])).

tff(c_2194,plain,(
    ! [A_229,B_230,C_231] :
      ( k2_relset_1(A_229,B_230,C_231) = k2_relat_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2336,plain,(
    ! [C_252] :
      ( k2_relset_1('#skF_1','#skF_2',C_252) = k2_relat_1(C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2052,c_2194])).

tff(c_2339,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2065,c_2336])).

tff(c_2349,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2339])).

tff(c_2499,plain,(
    ! [B_271,A_272] :
      ( m1_subset_1(B_271,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_271),A_272)))
      | ~ r1_tarski(k2_relat_1(B_271),A_272)
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2547,plain,(
    ! [B_275] :
      ( m1_subset_1(B_275,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_275),k1_xboole_0)
      | ~ v1_funct_1(B_275)
      | ~ v1_relat_1(B_275) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2499])).

tff(c_2550,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2349,c_2547])).

tff(c_2558,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_2550])).

tff(c_2561,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2558])).

tff(c_2676,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2672,c_2561])).

tff(c_2708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2676])).

tff(c_2710,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2604])).

tff(c_2790,plain,(
    ! [B_288,A_289,C_290] :
      ( k1_xboole_0 = B_288
      | k1_relset_1(A_289,B_288,C_290) = A_289
      | ~ v1_funct_2(C_290,A_289,B_288)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_289,B_288))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2796,plain,(
    ! [C_290] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_290) = '#skF_1'
      | ~ v1_funct_2(C_290,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_290,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2052,c_2790])).

tff(c_2865,plain,(
    ! [C_294] :
      ( k1_relset_1('#skF_1','#skF_2',C_294) = '#skF_1'
      | ~ v1_funct_2(C_294,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_294,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2710,c_2796])).

tff(c_2868,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2065,c_2865])).

tff(c_2879,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2255,c_2868])).

tff(c_2562,plain,(
    ! [B_276,A_277] :
      ( r1_tarski(B_276,k2_zfmisc_1(k1_relat_1(B_276),A_277))
      | ~ r1_tarski(k2_relat_1(B_276),A_277)
      | ~ v1_funct_1(B_276)
      | ~ v1_relat_1(B_276) ) ),
    inference(resolution,[status(thm)],[c_2499,c_18])).

tff(c_3368,plain,(
    ! [B_326,A_327] :
      ( k2_zfmisc_1(k1_relat_1(B_326),A_327) = B_326
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(B_326),A_327),B_326)
      | ~ r1_tarski(k2_relat_1(B_326),A_327)
      | ~ v1_funct_1(B_326)
      | ~ v1_relat_1(B_326) ) ),
    inference(resolution,[status(thm)],[c_2562,c_2])).

tff(c_3378,plain,(
    ! [B_326] :
      ( k2_zfmisc_1(k1_relat_1(B_326),k1_xboole_0) = B_326
      | ~ r1_tarski(k1_xboole_0,B_326)
      | ~ r1_tarski(k2_relat_1(B_326),k1_xboole_0)
      | ~ v1_funct_1(B_326)
      | ~ v1_relat_1(B_326) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3368])).

tff(c_3388,plain,(
    ! [B_328] :
      ( k1_xboole_0 = B_328
      | ~ r1_tarski(k2_relat_1(B_328),k1_xboole_0)
      | ~ v1_funct_1(B_328)
      | ~ v1_relat_1(B_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12,c_3378])).

tff(c_3404,plain,(
    ! [A_329] :
      ( k2_funct_1(A_329) = k1_xboole_0
      | ~ r1_tarski(k1_relat_1(A_329),k1_xboole_0)
      | ~ v1_funct_1(k2_funct_1(A_329))
      | ~ v1_relat_1(k2_funct_1(A_329))
      | ~ v2_funct_1(A_329)
      | ~ v1_funct_1(A_329)
      | ~ v1_relat_1(A_329) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3388])).

tff(c_3407,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2879,c_3404])).

tff(c_3415,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_68,c_177,c_3407])).

tff(c_3418,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3415])).

tff(c_3421,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_3418])).

tff(c_3425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_3421])).

tff(c_3427,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3415])).

tff(c_3538,plain,(
    ! [A_335,A_336] :
      ( m1_subset_1(k2_funct_1(A_335),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_335),A_336)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_335)),A_336)
      | ~ v1_funct_1(k2_funct_1(A_335))
      | ~ v1_relat_1(k2_funct_1(A_335))
      | ~ v2_funct_1(A_335)
      | ~ v1_funct_1(A_335)
      | ~ v1_relat_1(A_335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2499])).

tff(c_3564,plain,(
    ! [A_336] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_336)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_336)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2349,c_3538])).

tff(c_3597,plain,(
    ! [A_338] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_338)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_338) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_68,c_3427,c_177,c_3564])).

tff(c_3639,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3597,c_184])).

tff(c_3643,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3639])).

tff(c_3646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_68,c_6,c_2879,c_3643])).

tff(c_3648,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2558])).

tff(c_3675,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3648,c_244])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2070,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2052,c_10])).

tff(c_2095,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2070])).

tff(c_3700,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3675,c_2095])).

tff(c_3711,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3675,c_8])).

tff(c_3647,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_2558])).

tff(c_3769,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3675,c_3647])).

tff(c_3788,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3769,c_18])).

tff(c_3811,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_3788,c_2])).

tff(c_3820,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3711,c_3811])).

tff(c_3822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3700,c_3820])).

tff(c_3824,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2070])).

tff(c_3835,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_8])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3833,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_3824,c_28])).

tff(c_4108,plain,(
    ! [B_384,A_385] :
      ( v1_funct_2(B_384,k1_relat_1(B_384),A_385)
      | ~ r1_tarski(k2_relat_1(B_384),A_385)
      | ~ v1_funct_1(B_384)
      | ~ v1_relat_1(B_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4738,plain,(
    ! [A_452,A_453] :
      ( v1_funct_2(k2_funct_1(A_452),k2_relat_1(A_452),A_453)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_452)),A_453)
      | ~ v1_funct_1(k2_funct_1(A_452))
      | ~ v1_relat_1(k2_funct_1(A_452))
      | ~ v2_funct_1(A_452)
      | ~ v1_funct_1(A_452)
      | ~ v1_relat_1(A_452) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4108])).

tff(c_4747,plain,(
    ! [A_453] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',A_453)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_453)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3833,c_4738])).

tff(c_4750,plain,(
    ! [A_453] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',A_453)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_453)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_68,c_177,c_4747])).

tff(c_4751,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4750])).

tff(c_4754,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_4751])).

tff(c_4758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_4754])).

tff(c_4760,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4750])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3834,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_3824,c_30])).

tff(c_3832,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_3824,c_12])).

tff(c_4246,plain,(
    ! [B_405,A_406] :
      ( m1_subset_1(B_405,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_405),A_406)))
      | ~ r1_tarski(k2_relat_1(B_405),A_406)
      | ~ v1_funct_1(B_405)
      | ~ v1_relat_1(B_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4317,plain,(
    ! [B_412,A_413] :
      ( r1_tarski(B_412,k2_zfmisc_1(k1_relat_1(B_412),A_413))
      | ~ r1_tarski(k2_relat_1(B_412),A_413)
      | ~ v1_funct_1(B_412)
      | ~ v1_relat_1(B_412) ) ),
    inference(resolution,[status(thm)],[c_4246,c_18])).

tff(c_4713,plain,(
    ! [B_449,A_450] :
      ( k2_zfmisc_1(k1_relat_1(B_449),A_450) = B_449
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(B_449),A_450),B_449)
      | ~ r1_tarski(k2_relat_1(B_449),A_450)
      | ~ v1_funct_1(B_449)
      | ~ v1_relat_1(B_449) ) ),
    inference(resolution,[status(thm)],[c_4317,c_2])).

tff(c_4720,plain,(
    ! [B_449] :
      ( k2_zfmisc_1(k1_relat_1(B_449),'#skF_3') = B_449
      | ~ r1_tarski('#skF_3',B_449)
      | ~ r1_tarski(k2_relat_1(B_449),'#skF_3')
      | ~ v1_funct_1(B_449)
      | ~ v1_relat_1(B_449) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3832,c_4713])).

tff(c_4728,plain,(
    ! [B_451] :
      ( B_451 = '#skF_3'
      | ~ r1_tarski(k2_relat_1(B_451),'#skF_3')
      | ~ v1_funct_1(B_451)
      | ~ v1_relat_1(B_451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3835,c_3832,c_4720])).

tff(c_4761,plain,(
    ! [A_454] :
      ( k2_funct_1(A_454) = '#skF_3'
      | ~ r1_tarski(k1_relat_1(A_454),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(A_454))
      | ~ v1_relat_1(k2_funct_1(A_454))
      | ~ v2_funct_1(A_454)
      | ~ v1_funct_1(A_454)
      | ~ v1_relat_1(A_454) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4728])).

tff(c_4767,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3834,c_4761])).

tff(c_4769,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_74,c_68,c_4760,c_177,c_3835,c_4767])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3831,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_3824,c_14])).

tff(c_3823,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2070])).

tff(c_3889,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_3824,c_3823])).

tff(c_3890,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3889])).

tff(c_3893,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3890,c_184])).

tff(c_3955,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3831,c_3893])).

tff(c_3959,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_3955])).

tff(c_4771,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4769,c_3959])).

tff(c_4777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3835,c_4771])).

tff(c_4778,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3889])).

tff(c_4779,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3889])).

tff(c_4799,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4778,c_4779])).

tff(c_4783,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4778,c_4778,c_3833])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3830,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_16])).

tff(c_4780,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4778,c_3830])).

tff(c_4976,plain,(
    ! [A_480,B_481,C_482] :
      ( k2_relset_1(A_480,B_481,C_482) = k2_relat_1(C_482)
      | ~ m1_subset_1(C_482,k1_zfmisc_1(k2_zfmisc_1(A_480,B_481))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4980,plain,(
    ! [A_480,B_481] : k2_relset_1(A_480,B_481,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4780,c_4976])).

tff(c_4992,plain,(
    ! [A_480,B_481] : k2_relset_1(A_480,B_481,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4783,c_4980])).

tff(c_4791,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4778,c_66])).

tff(c_4994,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4992,c_4791])).

tff(c_4996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4799,c_4994])).

tff(c_4997,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_5186,plain,(
    ! [A_509,B_510,C_511] :
      ( k2_relset_1(A_509,B_510,C_511) = k2_relat_1(C_511)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(k2_zfmisc_1(A_509,B_510))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5196,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_5186])).

tff(c_5210,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5196])).

tff(c_4998,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_5245,plain,(
    ! [A_518,B_519,C_520] :
      ( k1_relset_1(A_518,B_519,C_520) = k1_relat_1(C_520)
      | ~ m1_subset_1(C_520,k1_zfmisc_1(k2_zfmisc_1(A_518,B_519))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_5266,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4998,c_5245])).

tff(c_5790,plain,(
    ! [B_572,C_573,A_574] :
      ( k1_xboole_0 = B_572
      | v1_funct_2(C_573,A_574,B_572)
      | k1_relset_1(A_574,B_572,C_573) != A_574
      | ~ m1_subset_1(C_573,k1_zfmisc_1(k2_zfmisc_1(A_574,B_572))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5799,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_4998,c_5790])).

tff(c_5820,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5266,c_5799])).

tff(c_5821,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_4997,c_5820])).

tff(c_5829,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5821])).

tff(c_5832,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5829])).

tff(c_5835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5051,c_74,c_68,c_5210,c_5832])).

tff(c_5836,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5821])).

tff(c_5870,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5836,c_8])).

tff(c_5867,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5836,c_5836,c_12])).

tff(c_5002,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4998,c_18])).

tff(c_5003,plain,(
    ! [B_483,A_484] :
      ( B_483 = A_484
      | ~ r1_tarski(B_483,A_484)
      | ~ r1_tarski(A_484,B_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5012,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5002,c_5003])).

tff(c_5088,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5012])).

tff(c_5954,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5867,c_5088])).

tff(c_5959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5870,c_5954])).

tff(c_5960,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5012])).

tff(c_6511,plain,(
    ! [B_647,A_648,C_649] :
      ( k1_xboole_0 = B_647
      | k1_relset_1(A_648,B_647,C_649) = A_648
      | ~ v1_funct_2(C_649,A_648,B_647)
      | ~ m1_subset_1(C_649,k1_zfmisc_1(k2_zfmisc_1(A_648,B_647))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_6517,plain,(
    ! [C_649] :
      ( k1_xboole_0 = '#skF_1'
      | k1_relset_1('#skF_2','#skF_1',C_649) = '#skF_2'
      | ~ v1_funct_2(C_649,'#skF_2','#skF_1')
      | ~ m1_subset_1(C_649,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5960,c_6511])).

tff(c_6941,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6517])).

tff(c_5968,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5960,c_10])).

tff(c_5987,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5968])).

tff(c_6966,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6941,c_5987])).

tff(c_6973,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6941,c_6941,c_12])).

tff(c_7102,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6973,c_5960])).

tff(c_7104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6966,c_7102])).

tff(c_7106,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6517])).

tff(c_6112,plain,(
    ! [A_598,B_599,C_600] :
      ( k1_relset_1(A_598,B_599,C_600) = k1_relat_1(C_600)
      | ~ m1_subset_1(C_600,k1_zfmisc_1(k2_zfmisc_1(A_598,B_599))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6295,plain,(
    ! [A_626,B_627,A_628] :
      ( k1_relset_1(A_626,B_627,A_628) = k1_relat_1(A_628)
      | ~ r1_tarski(A_628,k2_zfmisc_1(A_626,B_627)) ) ),
    inference(resolution,[status(thm)],[c_20,c_6112])).

tff(c_6318,plain,(
    ! [A_626,B_627] : k1_relset_1(A_626,B_627,k2_zfmisc_1(A_626,B_627)) = k1_relat_1(k2_zfmisc_1(A_626,B_627)) ),
    inference(resolution,[status(thm)],[c_6,c_6295])).

tff(c_6640,plain,(
    ! [B_655,C_656,A_657] :
      ( k1_xboole_0 = B_655
      | v1_funct_2(C_656,A_657,B_655)
      | k1_relset_1(A_657,B_655,C_656) != A_657
      | ~ m1_subset_1(C_656,k1_zfmisc_1(k2_zfmisc_1(A_657,B_655))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7131,plain,(
    ! [B_679,A_680,A_681] :
      ( k1_xboole_0 = B_679
      | v1_funct_2(A_680,A_681,B_679)
      | k1_relset_1(A_681,B_679,A_680) != A_681
      | ~ r1_tarski(A_680,k2_zfmisc_1(A_681,B_679)) ) ),
    inference(resolution,[status(thm)],[c_20,c_6640])).

tff(c_7153,plain,(
    ! [B_679,A_681] :
      ( k1_xboole_0 = B_679
      | v1_funct_2(k2_zfmisc_1(A_681,B_679),A_681,B_679)
      | k1_relset_1(A_681,B_679,k2_zfmisc_1(A_681,B_679)) != A_681 ) ),
    inference(resolution,[status(thm)],[c_6,c_7131])).

tff(c_7169,plain,(
    ! [B_682,A_683] :
      ( k1_xboole_0 = B_682
      | v1_funct_2(k2_zfmisc_1(A_683,B_682),A_683,B_682)
      | k1_relat_1(k2_zfmisc_1(A_683,B_682)) != A_683 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6318,c_7153])).

tff(c_7178,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_5960,c_7169])).

tff(c_7192,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5960,c_7178])).

tff(c_7193,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_4997,c_7106,c_7192])).

tff(c_7199,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_7193])).

tff(c_7202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5051,c_74,c_68,c_6109,c_7199])).

tff(c_7203,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5968])).

tff(c_7227,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7203])).

tff(c_7239,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7227,c_8])).

tff(c_7235,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7227,c_7227,c_14])).

tff(c_5013,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_5003])).

tff(c_5087,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5013])).

tff(c_7311,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7235,c_5087])).

tff(c_7316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7239,c_7311])).

tff(c_7317,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7203])).

tff(c_7340,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7317,c_8])).

tff(c_7337,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7317,c_7317,c_12])).

tff(c_7399,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7337,c_5087])).

tff(c_7404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7340,c_7399])).

tff(c_7405,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5013])).

tff(c_7408,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7405,c_70])).

tff(c_8233,plain,(
    ! [A_786,B_787,C_788] :
      ( k2_relset_1(A_786,B_787,C_788) = k2_relat_1(C_788)
      | ~ m1_subset_1(C_788,k1_zfmisc_1(k2_zfmisc_1(A_786,B_787))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8339,plain,(
    ! [C_801] :
      ( k2_relset_1('#skF_1','#skF_2',C_801) = k2_relat_1(C_801)
      | ~ m1_subset_1(C_801,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7405,c_8233])).

tff(c_8342,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7408,c_8339])).

tff(c_8352,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8342])).

tff(c_8158,plain,(
    ! [A_772,B_773,C_774] :
      ( k1_relset_1(A_772,B_773,C_774) = k1_relat_1(C_774)
      | ~ m1_subset_1(C_774,k1_zfmisc_1(k2_zfmisc_1(A_772,B_773))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8172,plain,(
    ! [A_772,B_773] : k1_relset_1(A_772,B_773,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_8158])).

tff(c_8181,plain,(
    ! [A_772,B_773] : k1_relset_1(A_772,B_773,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8172])).

tff(c_8652,plain,(
    ! [B_831,C_832,A_833] :
      ( k1_xboole_0 = B_831
      | v1_funct_2(C_832,A_833,B_831)
      | k1_relset_1(A_833,B_831,C_832) != A_833
      | ~ m1_subset_1(C_832,k1_zfmisc_1(k2_zfmisc_1(A_833,B_831))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8661,plain,(
    ! [C_832] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_832,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_832) != '#skF_1'
      | ~ m1_subset_1(C_832,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7405,c_8652])).

tff(c_8697,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8661])).

tff(c_8598,plain,(
    ! [B_828,A_829] :
      ( m1_subset_1(B_828,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_828),A_829)))
      | ~ r1_tarski(k2_relat_1(B_828),A_829)
      | ~ v1_funct_1(B_828)
      | ~ v1_relat_1(B_828) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8638,plain,(
    ! [B_830] :
      ( m1_subset_1(B_830,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_830),k1_xboole_0)
      | ~ v1_funct_1(B_830)
      | ~ v1_relat_1(B_830) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8598])).

tff(c_8641,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8352,c_8638])).

tff(c_8649,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5051,c_74,c_8641])).

tff(c_8681,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8649])).

tff(c_8699,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8697,c_8681])).

tff(c_8733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8699])).

tff(c_8736,plain,(
    ! [C_836] :
      ( v1_funct_2(C_836,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_836) != '#skF_1'
      | ~ m1_subset_1(C_836,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_8661])).

tff(c_8747,plain,
    ( v1_funct_2(k1_xboole_0,'#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2',k1_xboole_0) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_8736])).

tff(c_8752,plain,
    ( v1_funct_2(k1_xboole_0,'#skF_1','#skF_2')
    | k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8181,c_8747])).

tff(c_8753,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8752])).

tff(c_7525,plain,(
    ! [A_712,B_713,C_714] :
      ( k2_relset_1(A_712,B_713,C_714) = k2_relat_1(C_714)
      | ~ m1_subset_1(C_714,k1_zfmisc_1(k2_zfmisc_1(A_712,B_713))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_7649,plain,(
    ! [C_732] :
      ( k2_relset_1('#skF_1','#skF_2',C_732) = k2_relat_1(C_732)
      | ~ m1_subset_1(C_732,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7405,c_7525])).

tff(c_7652,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7408,c_7649])).

tff(c_7662,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_7652])).

tff(c_7603,plain,(
    ! [A_725,B_726,C_727] :
      ( k1_relset_1(A_725,B_726,C_727) = k1_relat_1(C_727)
      | ~ m1_subset_1(C_727,k1_zfmisc_1(k2_zfmisc_1(A_725,B_726))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_7624,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4998,c_7603])).

tff(c_7942,plain,(
    ! [B_765,C_766,A_767] :
      ( k1_xboole_0 = B_765
      | v1_funct_2(C_766,A_767,B_765)
      | k1_relset_1(A_767,B_765,C_766) != A_767
      | ~ m1_subset_1(C_766,k1_zfmisc_1(k2_zfmisc_1(A_767,B_765))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7951,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_4998,c_7942])).

tff(c_7968,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7624,c_7951])).

tff(c_7969,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_4997,c_7968])).

tff(c_7974,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7969])).

tff(c_7977,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_7974])).

tff(c_7980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5051,c_74,c_68,c_7662,c_7977])).

tff(c_7981,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7969])).

tff(c_8011,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7981,c_8])).

tff(c_8008,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7981,c_7981,c_12])).

tff(c_7524,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5012])).

tff(c_8114,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8008,c_7524])).

tff(c_8120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8011,c_8114])).

tff(c_8121,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5012])).

tff(c_8445,plain,(
    ! [A_811,B_812,A_813] :
      ( k1_relset_1(A_811,B_812,A_813) = k1_relat_1(A_813)
      | ~ r1_tarski(A_813,k2_zfmisc_1(A_811,B_812)) ) ),
    inference(resolution,[status(thm)],[c_20,c_8158])).

tff(c_8466,plain,(
    ! [A_811,B_812] : k1_relset_1(A_811,B_812,k2_zfmisc_1(A_811,B_812)) = k1_relat_1(k2_zfmisc_1(A_811,B_812)) ),
    inference(resolution,[status(thm)],[c_6,c_8445])).

tff(c_9258,plain,(
    ! [B_864,A_865,A_866] :
      ( k1_xboole_0 = B_864
      | v1_funct_2(A_865,A_866,B_864)
      | k1_relset_1(A_866,B_864,A_865) != A_866
      | ~ r1_tarski(A_865,k2_zfmisc_1(A_866,B_864)) ) ),
    inference(resolution,[status(thm)],[c_20,c_8652])).

tff(c_9280,plain,(
    ! [B_864,A_866] :
      ( k1_xboole_0 = B_864
      | v1_funct_2(k2_zfmisc_1(A_866,B_864),A_866,B_864)
      | k1_relset_1(A_866,B_864,k2_zfmisc_1(A_866,B_864)) != A_866 ) ),
    inference(resolution,[status(thm)],[c_6,c_9258])).

tff(c_9330,plain,(
    ! [B_870,A_871] :
      ( k1_xboole_0 = B_870
      | v1_funct_2(k2_zfmisc_1(A_871,B_870),A_871,B_870)
      | k1_relat_1(k2_zfmisc_1(A_871,B_870)) != A_871 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8466,c_9280])).

tff(c_9343,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_8121,c_9330])).

tff(c_9364,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8121,c_9343])).

tff(c_9365,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_4997,c_8753,c_9364])).

tff(c_9374,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_9365])).

tff(c_9377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5051,c_74,c_68,c_8352,c_9374])).

tff(c_9379,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8752])).

tff(c_8130,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8121,c_10])).

tff(c_8189,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8130])).

tff(c_9399,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9379,c_8189])).

tff(c_9410,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9379,c_9379,c_12])).

tff(c_9600,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9410,c_8121])).

tff(c_9602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9399,c_9600])).

tff(c_9603,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8130])).

tff(c_9683,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9603])).

tff(c_7413,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7405,c_10])).

tff(c_7432,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7413])).

tff(c_9692,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9683,c_7432])).

tff(c_9698,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9683,c_9683,c_14])).

tff(c_9764,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9698,c_7405])).

tff(c_9766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9692,c_9764])).

tff(c_9767,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9603])).

tff(c_9785,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9767,c_7432])).

tff(c_9904,plain,(
    ! [A_892] : k2_zfmisc_1(A_892,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9767,c_9767,c_12])).

tff(c_9914,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_9904,c_7405])).

tff(c_9923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9785,c_9914])).

tff(c_9925,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7413])).

tff(c_9935,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9925,c_8])).

tff(c_9933,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9925,c_9925,c_28])).

tff(c_9934,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9925,c_9925,c_30])).

tff(c_10309,plain,(
    ! [B_945,A_946] :
      ( v1_funct_2(B_945,k1_relat_1(B_945),A_946)
      | ~ r1_tarski(k2_relat_1(B_945),A_946)
      | ~ v1_funct_1(B_945)
      | ~ v1_relat_1(B_945) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10318,plain,(
    ! [A_946] :
      ( v1_funct_2('#skF_3','#skF_3',A_946)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_946)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9934,c_10309])).

tff(c_10321,plain,(
    ! [A_946] : v1_funct_2('#skF_3','#skF_3',A_946) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5051,c_74,c_9935,c_9933,c_10318])).

tff(c_9931,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9925,c_9925,c_14])).

tff(c_9924,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7413])).

tff(c_9969,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9925,c_9925,c_9924])).

tff(c_9970,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9969])).

tff(c_9972,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9970,c_5002])).

tff(c_10053,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9931,c_9972])).

tff(c_5018,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_5003])).

tff(c_9927,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9925,c_9925,c_5018])).

tff(c_10062,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10053,c_9927])).

tff(c_9974,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9970,c_4997])).

tff(c_10070,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10062,c_9974])).

tff(c_10324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10321,c_10070])).

tff(c_10325,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9969])).

tff(c_10326,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9969])).

tff(c_10348,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10325,c_10326])).

tff(c_46,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_76,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_46])).

tff(c_9928,plain,(
    ! [A_28] :
      ( v1_funct_2('#skF_3',A_28,'#skF_3')
      | A_28 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9925,c_9925,c_9925,c_76])).

tff(c_10521,plain,(
    ! [A_957] :
      ( v1_funct_2('#skF_1',A_957,'#skF_1')
      | A_957 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10325,c_10325,c_10325,c_9928])).

tff(c_9932,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9925,c_9925,c_12])).

tff(c_10375,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10325,c_10325,c_9932])).

tff(c_10336,plain,(
    r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10325,c_5002])).

tff(c_10471,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10375,c_10336])).

tff(c_10447,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10325,c_10325,c_9927])).

tff(c_10480,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10471,c_10447])).

tff(c_10338,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10325,c_4997])).

tff(c_10488,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10480,c_10338])).

tff(c_10524,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10521,c_10488])).

tff(c_10528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10348,c_10524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.49/2.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/2.87  
% 7.82/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/2.87  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.82/2.87  
% 7.82/2.87  %Foreground sorts:
% 7.82/2.87  
% 7.82/2.87  
% 7.82/2.87  %Background operators:
% 7.82/2.87  
% 7.82/2.87  
% 7.82/2.87  %Foreground operators:
% 7.82/2.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.82/2.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.82/2.87  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.82/2.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.82/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.82/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.82/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.82/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.82/2.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.82/2.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.82/2.87  tff('#skF_2', type, '#skF_2': $i).
% 7.82/2.87  tff('#skF_3', type, '#skF_3': $i).
% 7.82/2.87  tff('#skF_1', type, '#skF_1': $i).
% 7.82/2.87  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.82/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.82/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.82/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.82/2.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.82/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.82/2.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.82/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.82/2.87  
% 8.10/2.91  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.10/2.91  tff(f_145, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.10/2.91  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.10/2.91  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.10/2.91  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 8.10/2.91  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.10/2.91  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.10/2.91  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.10/2.91  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.10/2.91  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.10/2.91  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.10/2.91  tff(f_128, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 8.10/2.91  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.10/2.91  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 8.10/2.91  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.10/2.91  tff(c_26, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.10/2.91  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.91  tff(c_5032, plain, (![B_486, A_487]: (v1_relat_1(B_486) | ~m1_subset_1(B_486, k1_zfmisc_1(A_487)) | ~v1_relat_1(A_487))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.10/2.91  tff(c_5041, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_5032])).
% 8.10/2.91  tff(c_5051, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5041])).
% 8.10/2.91  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.91  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.91  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.91  tff(c_6086, plain, (![A_595, B_596, C_597]: (k2_relset_1(A_595, B_596, C_597)=k2_relat_1(C_597) | ~m1_subset_1(C_597, k1_zfmisc_1(k2_zfmisc_1(A_595, B_596))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.10/2.91  tff(c_6096, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_6086])).
% 8.10/2.91  tff(c_6109, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6096])).
% 8.10/2.91  tff(c_40, plain, (![A_21]: (k1_relat_1(k2_funct_1(A_21))=k2_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.10/2.91  tff(c_189, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.10/2.91  tff(c_195, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_189])).
% 8.10/2.91  tff(c_202, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_195])).
% 8.10/2.91  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.10/2.91  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.91  tff(c_420, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.10/2.91  tff(c_439, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_420])).
% 8.10/2.91  tff(c_683, plain, (![B_129, A_130, C_131]: (k1_xboole_0=B_129 | k1_relset_1(A_130, B_129, C_131)=A_130 | ~v1_funct_2(C_131, A_130, B_129) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.10/2.91  tff(c_693, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_683])).
% 8.10/2.91  tff(c_708, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_439, c_693])).
% 8.10/2.91  tff(c_712, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_708])).
% 8.10/2.91  tff(c_38, plain, (![A_21]: (k2_relat_1(k2_funct_1(A_21))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.10/2.91  tff(c_36, plain, (![A_20]: (v1_relat_1(k2_funct_1(A_20)) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.10/2.91  tff(c_142, plain, (![A_46]: (v1_funct_1(k2_funct_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.10/2.91  tff(c_64, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.91  tff(c_136, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 8.10/2.91  tff(c_145, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_142, c_136])).
% 8.10/2.91  tff(c_148, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_145])).
% 8.10/2.91  tff(c_160, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.10/2.91  tff(c_166, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_160])).
% 8.10/2.91  tff(c_173, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_166])).
% 8.10/2.91  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_173])).
% 8.10/2.91  tff(c_177, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_64])).
% 8.10/2.91  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.10/2.91  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.10/2.91  tff(c_628, plain, (![B_126, A_127]: (m1_subset_1(B_126, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_126), A_127))) | ~r1_tarski(k2_relat_1(B_126), A_127) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.10/2.91  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.10/2.91  tff(c_909, plain, (![B_147, A_148]: (r1_tarski(B_147, k2_zfmisc_1(k1_relat_1(B_147), A_148)) | ~r1_tarski(k2_relat_1(B_147), A_148) | ~v1_funct_1(B_147) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_628, c_18])).
% 8.10/2.91  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.10/2.91  tff(c_1286, plain, (![B_174, A_175]: (k2_zfmisc_1(k1_relat_1(B_174), A_175)=B_174 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(B_174), A_175), B_174) | ~r1_tarski(k2_relat_1(B_174), A_175) | ~v1_funct_1(B_174) | ~v1_relat_1(B_174))), inference(resolution, [status(thm)], [c_909, c_2])).
% 8.10/2.91  tff(c_1296, plain, (![B_174]: (k2_zfmisc_1(k1_relat_1(B_174), k1_xboole_0)=B_174 | ~r1_tarski(k1_xboole_0, B_174) | ~r1_tarski(k2_relat_1(B_174), k1_xboole_0) | ~v1_funct_1(B_174) | ~v1_relat_1(B_174))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1286])).
% 8.10/2.91  tff(c_1306, plain, (![B_176]: (k1_xboole_0=B_176 | ~r1_tarski(k2_relat_1(B_176), k1_xboole_0) | ~v1_funct_1(B_176) | ~v1_relat_1(B_176))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12, c_1296])).
% 8.10/2.91  tff(c_1321, plain, (![A_177]: (k2_funct_1(A_177)=k1_xboole_0 | ~r1_tarski(k1_relat_1(A_177), k1_xboole_0) | ~v1_funct_1(k2_funct_1(A_177)) | ~v1_relat_1(k2_funct_1(A_177)) | ~v2_funct_1(A_177) | ~v1_funct_1(A_177) | ~v1_relat_1(A_177))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1306])).
% 8.10/2.91  tff(c_1324, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_712, c_1321])).
% 8.10/2.91  tff(c_1332, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_68, c_177, c_1324])).
% 8.10/2.91  tff(c_1335, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1332])).
% 8.10/2.91  tff(c_1338, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1335])).
% 8.10/2.91  tff(c_1342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_1338])).
% 8.10/2.91  tff(c_1344, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1332])).
% 8.10/2.91  tff(c_337, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.10/2.91  tff(c_344, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_337])).
% 8.10/2.91  tff(c_357, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_344])).
% 8.10/2.91  tff(c_1466, plain, (![A_184, A_185]: (m1_subset_1(k2_funct_1(A_184), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_184), A_185))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_184)), A_185) | ~v1_funct_1(k2_funct_1(A_184)) | ~v1_relat_1(k2_funct_1(A_184)) | ~v2_funct_1(A_184) | ~v1_funct_1(A_184) | ~v1_relat_1(A_184))), inference(superposition, [status(thm), theory('equality')], [c_40, c_628])).
% 8.10/2.91  tff(c_1492, plain, (![A_185]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_185))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_185) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_357, c_1466])).
% 8.10/2.91  tff(c_1519, plain, (![A_186]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_186))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_186))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_68, c_1344, c_177, c_1492])).
% 8.10/2.91  tff(c_176, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_64])).
% 8.10/2.91  tff(c_184, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_176])).
% 8.10/2.91  tff(c_1561, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_1519, c_184])).
% 8.10/2.91  tff(c_1565, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_1561])).
% 8.10/2.91  tff(c_1568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_68, c_6, c_712, c_1565])).
% 8.10/2.91  tff(c_1569, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_708])).
% 8.10/2.91  tff(c_668, plain, (![B_128]: (m1_subset_1(B_128, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_128), k1_xboole_0) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(superposition, [status(thm), theory('equality')], [c_12, c_628])).
% 8.10/2.91  tff(c_671, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_357, c_668])).
% 8.10/2.91  tff(c_679, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_671])).
% 8.10/2.91  tff(c_682, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_679])).
% 8.10/2.91  tff(c_1572, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1569, c_682])).
% 8.10/2.91  tff(c_1603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1572])).
% 8.10/2.91  tff(c_1605, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_679])).
% 8.10/2.91  tff(c_232, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.10/2.91  tff(c_244, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_232])).
% 8.10/2.91  tff(c_1632, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1605, c_244])).
% 8.10/2.91  tff(c_1667, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1632, c_8])).
% 8.10/2.91  tff(c_1604, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_679])).
% 8.10/2.91  tff(c_1736, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1632, c_1604])).
% 8.10/2.91  tff(c_1755, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1736, c_18])).
% 8.10/2.91  tff(c_1760, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1755, c_2])).
% 8.10/2.91  tff(c_1769, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1667, c_1760])).
% 8.10/2.91  tff(c_1664, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1632, c_1632, c_12])).
% 8.10/2.91  tff(c_1857, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_1769, c_1664])).
% 8.10/2.91  tff(c_126, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.10/2.91  tff(c_133, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_126])).
% 8.10/2.91  tff(c_239, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_133, c_232])).
% 8.10/2.91  tff(c_258, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_239])).
% 8.10/2.91  tff(c_1785, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_258])).
% 8.10/2.91  tff(c_2051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1857, c_1785])).
% 8.10/2.91  tff(c_2052, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_239])).
% 8.10/2.91  tff(c_2065, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2052, c_70])).
% 8.10/2.91  tff(c_2156, plain, (![A_222, B_223, C_224]: (k1_relset_1(A_222, B_223, C_224)=k1_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.10/2.91  tff(c_2243, plain, (![C_238]: (k1_relset_1('#skF_1', '#skF_2', C_238)=k1_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2052, c_2156])).
% 8.10/2.91  tff(c_2255, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2065, c_2243])).
% 8.10/2.91  tff(c_2598, plain, (![B_278, C_279, A_280]: (k1_xboole_0=B_278 | v1_funct_2(C_279, A_280, B_278) | k1_relset_1(A_280, B_278, C_279)!=A_280 | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_280, B_278))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.10/2.91  tff(c_2604, plain, (![C_279]: (k1_xboole_0='#skF_2' | v1_funct_2(C_279, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_279)!='#skF_1' | ~m1_subset_1(C_279, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2052, c_2598])).
% 8.10/2.91  tff(c_2672, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2604])).
% 8.10/2.91  tff(c_2194, plain, (![A_229, B_230, C_231]: (k2_relset_1(A_229, B_230, C_231)=k2_relat_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.10/2.91  tff(c_2336, plain, (![C_252]: (k2_relset_1('#skF_1', '#skF_2', C_252)=k2_relat_1(C_252) | ~m1_subset_1(C_252, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2052, c_2194])).
% 8.10/2.91  tff(c_2339, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2065, c_2336])).
% 8.10/2.91  tff(c_2349, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2339])).
% 8.10/2.91  tff(c_2499, plain, (![B_271, A_272]: (m1_subset_1(B_271, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_271), A_272))) | ~r1_tarski(k2_relat_1(B_271), A_272) | ~v1_funct_1(B_271) | ~v1_relat_1(B_271))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.10/2.91  tff(c_2547, plain, (![B_275]: (m1_subset_1(B_275, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_275), k1_xboole_0) | ~v1_funct_1(B_275) | ~v1_relat_1(B_275))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2499])).
% 8.10/2.91  tff(c_2550, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2349, c_2547])).
% 8.10/2.91  tff(c_2558, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_2550])).
% 8.10/2.91  tff(c_2561, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2558])).
% 8.10/2.91  tff(c_2676, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2672, c_2561])).
% 8.10/2.91  tff(c_2708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2676])).
% 8.10/2.91  tff(c_2710, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2604])).
% 8.10/2.91  tff(c_2790, plain, (![B_288, A_289, C_290]: (k1_xboole_0=B_288 | k1_relset_1(A_289, B_288, C_290)=A_289 | ~v1_funct_2(C_290, A_289, B_288) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_289, B_288))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.10/2.91  tff(c_2796, plain, (![C_290]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_290)='#skF_1' | ~v1_funct_2(C_290, '#skF_1', '#skF_2') | ~m1_subset_1(C_290, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2052, c_2790])).
% 8.10/2.91  tff(c_2865, plain, (![C_294]: (k1_relset_1('#skF_1', '#skF_2', C_294)='#skF_1' | ~v1_funct_2(C_294, '#skF_1', '#skF_2') | ~m1_subset_1(C_294, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_2710, c_2796])).
% 8.10/2.91  tff(c_2868, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2065, c_2865])).
% 8.10/2.91  tff(c_2879, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2255, c_2868])).
% 8.10/2.91  tff(c_2562, plain, (![B_276, A_277]: (r1_tarski(B_276, k2_zfmisc_1(k1_relat_1(B_276), A_277)) | ~r1_tarski(k2_relat_1(B_276), A_277) | ~v1_funct_1(B_276) | ~v1_relat_1(B_276))), inference(resolution, [status(thm)], [c_2499, c_18])).
% 8.10/2.91  tff(c_3368, plain, (![B_326, A_327]: (k2_zfmisc_1(k1_relat_1(B_326), A_327)=B_326 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(B_326), A_327), B_326) | ~r1_tarski(k2_relat_1(B_326), A_327) | ~v1_funct_1(B_326) | ~v1_relat_1(B_326))), inference(resolution, [status(thm)], [c_2562, c_2])).
% 8.10/2.91  tff(c_3378, plain, (![B_326]: (k2_zfmisc_1(k1_relat_1(B_326), k1_xboole_0)=B_326 | ~r1_tarski(k1_xboole_0, B_326) | ~r1_tarski(k2_relat_1(B_326), k1_xboole_0) | ~v1_funct_1(B_326) | ~v1_relat_1(B_326))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3368])).
% 8.10/2.91  tff(c_3388, plain, (![B_328]: (k1_xboole_0=B_328 | ~r1_tarski(k2_relat_1(B_328), k1_xboole_0) | ~v1_funct_1(B_328) | ~v1_relat_1(B_328))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12, c_3378])).
% 8.10/2.91  tff(c_3404, plain, (![A_329]: (k2_funct_1(A_329)=k1_xboole_0 | ~r1_tarski(k1_relat_1(A_329), k1_xboole_0) | ~v1_funct_1(k2_funct_1(A_329)) | ~v1_relat_1(k2_funct_1(A_329)) | ~v2_funct_1(A_329) | ~v1_funct_1(A_329) | ~v1_relat_1(A_329))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3388])).
% 8.10/2.91  tff(c_3407, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2879, c_3404])).
% 8.10/2.91  tff(c_3415, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_68, c_177, c_3407])).
% 8.10/2.91  tff(c_3418, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3415])).
% 8.10/2.91  tff(c_3421, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_3418])).
% 8.10/2.91  tff(c_3425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_3421])).
% 8.10/2.91  tff(c_3427, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3415])).
% 8.10/2.91  tff(c_3538, plain, (![A_335, A_336]: (m1_subset_1(k2_funct_1(A_335), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_335), A_336))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_335)), A_336) | ~v1_funct_1(k2_funct_1(A_335)) | ~v1_relat_1(k2_funct_1(A_335)) | ~v2_funct_1(A_335) | ~v1_funct_1(A_335) | ~v1_relat_1(A_335))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2499])).
% 8.10/2.91  tff(c_3564, plain, (![A_336]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_336))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_336) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2349, c_3538])).
% 8.10/2.91  tff(c_3597, plain, (![A_338]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_338))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_338))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_68, c_3427, c_177, c_3564])).
% 8.10/2.91  tff(c_3639, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_3597, c_184])).
% 8.10/2.91  tff(c_3643, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_3639])).
% 8.10/2.91  tff(c_3646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_68, c_6, c_2879, c_3643])).
% 8.10/2.91  tff(c_3648, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2558])).
% 8.10/2.91  tff(c_3675, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_3648, c_244])).
% 8.10/2.91  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.10/2.91  tff(c_2070, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2052, c_10])).
% 8.10/2.91  tff(c_2095, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_2070])).
% 8.10/2.91  tff(c_3700, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3675, c_2095])).
% 8.10/2.91  tff(c_3711, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3675, c_8])).
% 8.10/2.91  tff(c_3647, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_2558])).
% 8.10/2.91  tff(c_3769, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3675, c_3647])).
% 8.10/2.91  tff(c_3788, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3769, c_18])).
% 8.10/2.91  tff(c_3811, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_3788, c_2])).
% 8.10/2.91  tff(c_3820, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3711, c_3811])).
% 8.10/2.91  tff(c_3822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3700, c_3820])).
% 8.10/2.91  tff(c_3824, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2070])).
% 8.10/2.91  tff(c_3835, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_8])).
% 8.10/2.91  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.10/2.91  tff(c_3833, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_3824, c_28])).
% 8.10/2.91  tff(c_4108, plain, (![B_384, A_385]: (v1_funct_2(B_384, k1_relat_1(B_384), A_385) | ~r1_tarski(k2_relat_1(B_384), A_385) | ~v1_funct_1(B_384) | ~v1_relat_1(B_384))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.10/2.91  tff(c_4738, plain, (![A_452, A_453]: (v1_funct_2(k2_funct_1(A_452), k2_relat_1(A_452), A_453) | ~r1_tarski(k2_relat_1(k2_funct_1(A_452)), A_453) | ~v1_funct_1(k2_funct_1(A_452)) | ~v1_relat_1(k2_funct_1(A_452)) | ~v2_funct_1(A_452) | ~v1_funct_1(A_452) | ~v1_relat_1(A_452))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4108])).
% 8.10/2.91  tff(c_4747, plain, (![A_453]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', A_453) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_453) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3833, c_4738])).
% 8.10/2.91  tff(c_4750, plain, (![A_453]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', A_453) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_453) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_68, c_177, c_4747])).
% 8.10/2.91  tff(c_4751, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4750])).
% 8.10/2.91  tff(c_4754, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_4751])).
% 8.10/2.91  tff(c_4758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_4754])).
% 8.10/2.91  tff(c_4760, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4750])).
% 8.10/2.91  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.10/2.91  tff(c_3834, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_3824, c_30])).
% 8.10/2.91  tff(c_3832, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_3824, c_12])).
% 8.10/2.91  tff(c_4246, plain, (![B_405, A_406]: (m1_subset_1(B_405, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_405), A_406))) | ~r1_tarski(k2_relat_1(B_405), A_406) | ~v1_funct_1(B_405) | ~v1_relat_1(B_405))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.10/2.91  tff(c_4317, plain, (![B_412, A_413]: (r1_tarski(B_412, k2_zfmisc_1(k1_relat_1(B_412), A_413)) | ~r1_tarski(k2_relat_1(B_412), A_413) | ~v1_funct_1(B_412) | ~v1_relat_1(B_412))), inference(resolution, [status(thm)], [c_4246, c_18])).
% 8.10/2.91  tff(c_4713, plain, (![B_449, A_450]: (k2_zfmisc_1(k1_relat_1(B_449), A_450)=B_449 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(B_449), A_450), B_449) | ~r1_tarski(k2_relat_1(B_449), A_450) | ~v1_funct_1(B_449) | ~v1_relat_1(B_449))), inference(resolution, [status(thm)], [c_4317, c_2])).
% 8.10/2.91  tff(c_4720, plain, (![B_449]: (k2_zfmisc_1(k1_relat_1(B_449), '#skF_3')=B_449 | ~r1_tarski('#skF_3', B_449) | ~r1_tarski(k2_relat_1(B_449), '#skF_3') | ~v1_funct_1(B_449) | ~v1_relat_1(B_449))), inference(superposition, [status(thm), theory('equality')], [c_3832, c_4713])).
% 8.10/2.91  tff(c_4728, plain, (![B_451]: (B_451='#skF_3' | ~r1_tarski(k2_relat_1(B_451), '#skF_3') | ~v1_funct_1(B_451) | ~v1_relat_1(B_451))), inference(demodulation, [status(thm), theory('equality')], [c_3835, c_3832, c_4720])).
% 8.10/2.91  tff(c_4761, plain, (![A_454]: (k2_funct_1(A_454)='#skF_3' | ~r1_tarski(k1_relat_1(A_454), '#skF_3') | ~v1_funct_1(k2_funct_1(A_454)) | ~v1_relat_1(k2_funct_1(A_454)) | ~v2_funct_1(A_454) | ~v1_funct_1(A_454) | ~v1_relat_1(A_454))), inference(superposition, [status(thm), theory('equality')], [c_38, c_4728])).
% 8.10/2.91  tff(c_4767, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3834, c_4761])).
% 8.10/2.91  tff(c_4769, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_202, c_74, c_68, c_4760, c_177, c_3835, c_4767])).
% 8.10/2.91  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.10/2.91  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.10/2.91  tff(c_3831, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_3824, c_14])).
% 8.10/2.91  tff(c_3823, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2070])).
% 8.10/2.91  tff(c_3889, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_3824, c_3823])).
% 8.10/2.91  tff(c_3890, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_3889])).
% 8.10/2.91  tff(c_3893, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3890, c_184])).
% 8.10/2.91  tff(c_3955, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3831, c_3893])).
% 8.10/2.91  tff(c_3959, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_20, c_3955])).
% 8.10/2.91  tff(c_4771, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4769, c_3959])).
% 8.10/2.91  tff(c_4777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3835, c_4771])).
% 8.10/2.91  tff(c_4778, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_3889])).
% 8.10/2.91  tff(c_4779, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_3889])).
% 8.10/2.91  tff(c_4799, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4778, c_4779])).
% 8.10/2.91  tff(c_4783, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4778, c_4778, c_3833])).
% 8.10/2.91  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.10/2.91  tff(c_3830, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_16])).
% 8.10/2.91  tff(c_4780, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_4778, c_3830])).
% 8.10/2.91  tff(c_4976, plain, (![A_480, B_481, C_482]: (k2_relset_1(A_480, B_481, C_482)=k2_relat_1(C_482) | ~m1_subset_1(C_482, k1_zfmisc_1(k2_zfmisc_1(A_480, B_481))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.10/2.91  tff(c_4980, plain, (![A_480, B_481]: (k2_relset_1(A_480, B_481, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_4780, c_4976])).
% 8.10/2.91  tff(c_4992, plain, (![A_480, B_481]: (k2_relset_1(A_480, B_481, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4783, c_4980])).
% 8.10/2.91  tff(c_4791, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4778, c_66])).
% 8.10/2.91  tff(c_4994, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4992, c_4791])).
% 8.10/2.91  tff(c_4996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4799, c_4994])).
% 8.10/2.91  tff(c_4997, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_176])).
% 8.10/2.91  tff(c_5186, plain, (![A_509, B_510, C_511]: (k2_relset_1(A_509, B_510, C_511)=k2_relat_1(C_511) | ~m1_subset_1(C_511, k1_zfmisc_1(k2_zfmisc_1(A_509, B_510))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.10/2.91  tff(c_5196, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_5186])).
% 8.10/2.91  tff(c_5210, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5196])).
% 8.10/2.91  tff(c_4998, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_176])).
% 8.10/2.91  tff(c_5245, plain, (![A_518, B_519, C_520]: (k1_relset_1(A_518, B_519, C_520)=k1_relat_1(C_520) | ~m1_subset_1(C_520, k1_zfmisc_1(k2_zfmisc_1(A_518, B_519))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.10/2.91  tff(c_5266, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_4998, c_5245])).
% 8.10/2.91  tff(c_5790, plain, (![B_572, C_573, A_574]: (k1_xboole_0=B_572 | v1_funct_2(C_573, A_574, B_572) | k1_relset_1(A_574, B_572, C_573)!=A_574 | ~m1_subset_1(C_573, k1_zfmisc_1(k2_zfmisc_1(A_574, B_572))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.10/2.91  tff(c_5799, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_4998, c_5790])).
% 8.10/2.91  tff(c_5820, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5266, c_5799])).
% 8.10/2.91  tff(c_5821, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_4997, c_5820])).
% 8.10/2.91  tff(c_5829, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_5821])).
% 8.10/2.91  tff(c_5832, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_5829])).
% 8.10/2.91  tff(c_5835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5051, c_74, c_68, c_5210, c_5832])).
% 8.10/2.91  tff(c_5836, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5821])).
% 8.10/2.91  tff(c_5870, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5836, c_8])).
% 8.10/2.91  tff(c_5867, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5836, c_5836, c_12])).
% 8.10/2.91  tff(c_5002, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_4998, c_18])).
% 8.10/2.91  tff(c_5003, plain, (![B_483, A_484]: (B_483=A_484 | ~r1_tarski(B_483, A_484) | ~r1_tarski(A_484, B_483))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.10/2.91  tff(c_5012, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5002, c_5003])).
% 8.10/2.91  tff(c_5088, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5012])).
% 8.10/2.91  tff(c_5954, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5867, c_5088])).
% 8.10/2.91  tff(c_5959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5870, c_5954])).
% 8.10/2.91  tff(c_5960, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_5012])).
% 8.10/2.91  tff(c_6511, plain, (![B_647, A_648, C_649]: (k1_xboole_0=B_647 | k1_relset_1(A_648, B_647, C_649)=A_648 | ~v1_funct_2(C_649, A_648, B_647) | ~m1_subset_1(C_649, k1_zfmisc_1(k2_zfmisc_1(A_648, B_647))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.10/2.91  tff(c_6517, plain, (![C_649]: (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', C_649)='#skF_2' | ~v1_funct_2(C_649, '#skF_2', '#skF_1') | ~m1_subset_1(C_649, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_5960, c_6511])).
% 8.10/2.91  tff(c_6941, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_6517])).
% 8.10/2.91  tff(c_5968, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5960, c_10])).
% 8.10/2.91  tff(c_5987, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5968])).
% 8.10/2.91  tff(c_6966, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6941, c_5987])).
% 8.10/2.91  tff(c_6973, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6941, c_6941, c_12])).
% 8.10/2.91  tff(c_7102, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6973, c_5960])).
% 8.10/2.91  tff(c_7104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6966, c_7102])).
% 8.10/2.91  tff(c_7106, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_6517])).
% 8.10/2.91  tff(c_6112, plain, (![A_598, B_599, C_600]: (k1_relset_1(A_598, B_599, C_600)=k1_relat_1(C_600) | ~m1_subset_1(C_600, k1_zfmisc_1(k2_zfmisc_1(A_598, B_599))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.10/2.91  tff(c_6295, plain, (![A_626, B_627, A_628]: (k1_relset_1(A_626, B_627, A_628)=k1_relat_1(A_628) | ~r1_tarski(A_628, k2_zfmisc_1(A_626, B_627)))), inference(resolution, [status(thm)], [c_20, c_6112])).
% 8.10/2.91  tff(c_6318, plain, (![A_626, B_627]: (k1_relset_1(A_626, B_627, k2_zfmisc_1(A_626, B_627))=k1_relat_1(k2_zfmisc_1(A_626, B_627)))), inference(resolution, [status(thm)], [c_6, c_6295])).
% 8.10/2.91  tff(c_6640, plain, (![B_655, C_656, A_657]: (k1_xboole_0=B_655 | v1_funct_2(C_656, A_657, B_655) | k1_relset_1(A_657, B_655, C_656)!=A_657 | ~m1_subset_1(C_656, k1_zfmisc_1(k2_zfmisc_1(A_657, B_655))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.10/2.91  tff(c_7131, plain, (![B_679, A_680, A_681]: (k1_xboole_0=B_679 | v1_funct_2(A_680, A_681, B_679) | k1_relset_1(A_681, B_679, A_680)!=A_681 | ~r1_tarski(A_680, k2_zfmisc_1(A_681, B_679)))), inference(resolution, [status(thm)], [c_20, c_6640])).
% 8.10/2.91  tff(c_7153, plain, (![B_679, A_681]: (k1_xboole_0=B_679 | v1_funct_2(k2_zfmisc_1(A_681, B_679), A_681, B_679) | k1_relset_1(A_681, B_679, k2_zfmisc_1(A_681, B_679))!=A_681)), inference(resolution, [status(thm)], [c_6, c_7131])).
% 8.10/2.91  tff(c_7169, plain, (![B_682, A_683]: (k1_xboole_0=B_682 | v1_funct_2(k2_zfmisc_1(A_683, B_682), A_683, B_682) | k1_relat_1(k2_zfmisc_1(A_683, B_682))!=A_683)), inference(demodulation, [status(thm), theory('equality')], [c_6318, c_7153])).
% 8.10/2.91  tff(c_7178, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_5960, c_7169])).
% 8.10/2.91  tff(c_7192, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5960, c_7178])).
% 8.10/2.91  tff(c_7193, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_4997, c_7106, c_7192])).
% 8.10/2.91  tff(c_7199, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_7193])).
% 8.10/2.91  tff(c_7202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5051, c_74, c_68, c_6109, c_7199])).
% 8.10/2.91  tff(c_7203, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5968])).
% 8.10/2.91  tff(c_7227, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_7203])).
% 8.10/2.91  tff(c_7239, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7227, c_8])).
% 8.10/2.91  tff(c_7235, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7227, c_7227, c_14])).
% 8.10/2.91  tff(c_5013, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_133, c_5003])).
% 8.10/2.91  tff(c_5087, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5013])).
% 8.10/2.91  tff(c_7311, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7235, c_5087])).
% 8.10/2.91  tff(c_7316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7239, c_7311])).
% 8.10/2.91  tff(c_7317, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7203])).
% 8.10/2.91  tff(c_7340, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7317, c_8])).
% 8.10/2.91  tff(c_7337, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7317, c_7317, c_12])).
% 8.10/2.91  tff(c_7399, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7337, c_5087])).
% 8.10/2.91  tff(c_7404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7340, c_7399])).
% 8.10/2.91  tff(c_7405, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_5013])).
% 8.10/2.91  tff(c_7408, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7405, c_70])).
% 8.10/2.91  tff(c_8233, plain, (![A_786, B_787, C_788]: (k2_relset_1(A_786, B_787, C_788)=k2_relat_1(C_788) | ~m1_subset_1(C_788, k1_zfmisc_1(k2_zfmisc_1(A_786, B_787))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.10/2.91  tff(c_8339, plain, (![C_801]: (k2_relset_1('#skF_1', '#skF_2', C_801)=k2_relat_1(C_801) | ~m1_subset_1(C_801, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7405, c_8233])).
% 8.10/2.91  tff(c_8342, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7408, c_8339])).
% 8.10/2.91  tff(c_8352, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8342])).
% 8.10/2.91  tff(c_8158, plain, (![A_772, B_773, C_774]: (k1_relset_1(A_772, B_773, C_774)=k1_relat_1(C_774) | ~m1_subset_1(C_774, k1_zfmisc_1(k2_zfmisc_1(A_772, B_773))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.10/2.91  tff(c_8172, plain, (![A_772, B_773]: (k1_relset_1(A_772, B_773, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_8158])).
% 8.10/2.91  tff(c_8181, plain, (![A_772, B_773]: (k1_relset_1(A_772, B_773, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8172])).
% 8.10/2.91  tff(c_8652, plain, (![B_831, C_832, A_833]: (k1_xboole_0=B_831 | v1_funct_2(C_832, A_833, B_831) | k1_relset_1(A_833, B_831, C_832)!=A_833 | ~m1_subset_1(C_832, k1_zfmisc_1(k2_zfmisc_1(A_833, B_831))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.10/2.91  tff(c_8661, plain, (![C_832]: (k1_xboole_0='#skF_2' | v1_funct_2(C_832, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_832)!='#skF_1' | ~m1_subset_1(C_832, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7405, c_8652])).
% 8.10/2.91  tff(c_8697, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_8661])).
% 8.10/2.91  tff(c_8598, plain, (![B_828, A_829]: (m1_subset_1(B_828, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_828), A_829))) | ~r1_tarski(k2_relat_1(B_828), A_829) | ~v1_funct_1(B_828) | ~v1_relat_1(B_828))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.10/2.91  tff(c_8638, plain, (![B_830]: (m1_subset_1(B_830, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_830), k1_xboole_0) | ~v1_funct_1(B_830) | ~v1_relat_1(B_830))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8598])).
% 8.10/2.91  tff(c_8641, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8352, c_8638])).
% 8.10/2.91  tff(c_8649, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5051, c_74, c_8641])).
% 8.10/2.91  tff(c_8681, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8649])).
% 8.10/2.91  tff(c_8699, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8697, c_8681])).
% 8.10/2.91  tff(c_8733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8699])).
% 8.10/2.91  tff(c_8736, plain, (![C_836]: (v1_funct_2(C_836, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_836)!='#skF_1' | ~m1_subset_1(C_836, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_8661])).
% 8.10/2.91  tff(c_8747, plain, (v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', k1_xboole_0)!='#skF_1'), inference(resolution, [status(thm)], [c_16, c_8736])).
% 8.10/2.91  tff(c_8752, plain, (v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2') | k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8181, c_8747])).
% 8.10/2.91  tff(c_8753, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_8752])).
% 8.10/2.91  tff(c_7525, plain, (![A_712, B_713, C_714]: (k2_relset_1(A_712, B_713, C_714)=k2_relat_1(C_714) | ~m1_subset_1(C_714, k1_zfmisc_1(k2_zfmisc_1(A_712, B_713))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.10/2.91  tff(c_7649, plain, (![C_732]: (k2_relset_1('#skF_1', '#skF_2', C_732)=k2_relat_1(C_732) | ~m1_subset_1(C_732, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7405, c_7525])).
% 8.10/2.91  tff(c_7652, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7408, c_7649])).
% 8.10/2.91  tff(c_7662, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_7652])).
% 8.10/2.91  tff(c_7603, plain, (![A_725, B_726, C_727]: (k1_relset_1(A_725, B_726, C_727)=k1_relat_1(C_727) | ~m1_subset_1(C_727, k1_zfmisc_1(k2_zfmisc_1(A_725, B_726))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.10/2.91  tff(c_7624, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_4998, c_7603])).
% 8.10/2.91  tff(c_7942, plain, (![B_765, C_766, A_767]: (k1_xboole_0=B_765 | v1_funct_2(C_766, A_767, B_765) | k1_relset_1(A_767, B_765, C_766)!=A_767 | ~m1_subset_1(C_766, k1_zfmisc_1(k2_zfmisc_1(A_767, B_765))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.10/2.91  tff(c_7951, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_4998, c_7942])).
% 8.10/2.91  tff(c_7968, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7624, c_7951])).
% 8.10/2.91  tff(c_7969, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_4997, c_7968])).
% 8.10/2.91  tff(c_7974, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_7969])).
% 8.10/2.91  tff(c_7977, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_7974])).
% 8.10/2.91  tff(c_7980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5051, c_74, c_68, c_7662, c_7977])).
% 8.10/2.91  tff(c_7981, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_7969])).
% 8.10/2.91  tff(c_8011, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7981, c_8])).
% 8.10/2.91  tff(c_8008, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7981, c_7981, c_12])).
% 8.10/2.91  tff(c_7524, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5012])).
% 8.10/2.91  tff(c_8114, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8008, c_7524])).
% 8.10/2.91  tff(c_8120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8011, c_8114])).
% 8.10/2.91  tff(c_8121, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_5012])).
% 8.10/2.91  tff(c_8445, plain, (![A_811, B_812, A_813]: (k1_relset_1(A_811, B_812, A_813)=k1_relat_1(A_813) | ~r1_tarski(A_813, k2_zfmisc_1(A_811, B_812)))), inference(resolution, [status(thm)], [c_20, c_8158])).
% 8.10/2.91  tff(c_8466, plain, (![A_811, B_812]: (k1_relset_1(A_811, B_812, k2_zfmisc_1(A_811, B_812))=k1_relat_1(k2_zfmisc_1(A_811, B_812)))), inference(resolution, [status(thm)], [c_6, c_8445])).
% 8.10/2.91  tff(c_9258, plain, (![B_864, A_865, A_866]: (k1_xboole_0=B_864 | v1_funct_2(A_865, A_866, B_864) | k1_relset_1(A_866, B_864, A_865)!=A_866 | ~r1_tarski(A_865, k2_zfmisc_1(A_866, B_864)))), inference(resolution, [status(thm)], [c_20, c_8652])).
% 8.10/2.91  tff(c_9280, plain, (![B_864, A_866]: (k1_xboole_0=B_864 | v1_funct_2(k2_zfmisc_1(A_866, B_864), A_866, B_864) | k1_relset_1(A_866, B_864, k2_zfmisc_1(A_866, B_864))!=A_866)), inference(resolution, [status(thm)], [c_6, c_9258])).
% 8.10/2.91  tff(c_9330, plain, (![B_870, A_871]: (k1_xboole_0=B_870 | v1_funct_2(k2_zfmisc_1(A_871, B_870), A_871, B_870) | k1_relat_1(k2_zfmisc_1(A_871, B_870))!=A_871)), inference(demodulation, [status(thm), theory('equality')], [c_8466, c_9280])).
% 8.10/2.91  tff(c_9343, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_8121, c_9330])).
% 8.10/2.91  tff(c_9364, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8121, c_9343])).
% 8.10/2.91  tff(c_9365, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_4997, c_8753, c_9364])).
% 8.10/2.91  tff(c_9374, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_9365])).
% 8.10/2.91  tff(c_9377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5051, c_74, c_68, c_8352, c_9374])).
% 8.10/2.91  tff(c_9379, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_8752])).
% 8.10/2.91  tff(c_8130, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8121, c_10])).
% 8.10/2.91  tff(c_8189, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8130])).
% 8.10/2.91  tff(c_9399, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9379, c_8189])).
% 8.10/2.91  tff(c_9410, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9379, c_9379, c_12])).
% 8.10/2.91  tff(c_9600, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9410, c_8121])).
% 8.10/2.91  tff(c_9602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9399, c_9600])).
% 8.10/2.91  tff(c_9603, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_8130])).
% 8.10/2.91  tff(c_9683, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_9603])).
% 8.10/2.91  tff(c_7413, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7405, c_10])).
% 8.10/2.91  tff(c_7432, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_7413])).
% 8.10/2.91  tff(c_9692, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9683, c_7432])).
% 8.10/2.91  tff(c_9698, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9683, c_9683, c_14])).
% 8.10/2.91  tff(c_9764, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9698, c_7405])).
% 8.10/2.91  tff(c_9766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9692, c_9764])).
% 8.10/2.91  tff(c_9767, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_9603])).
% 8.10/2.91  tff(c_9785, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9767, c_7432])).
% 8.10/2.91  tff(c_9904, plain, (![A_892]: (k2_zfmisc_1(A_892, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9767, c_9767, c_12])).
% 8.10/2.91  tff(c_9914, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_9904, c_7405])).
% 8.10/2.91  tff(c_9923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9785, c_9914])).
% 8.10/2.91  tff(c_9925, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_7413])).
% 8.10/2.91  tff(c_9935, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9925, c_8])).
% 8.10/2.91  tff(c_9933, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9925, c_9925, c_28])).
% 8.10/2.91  tff(c_9934, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9925, c_9925, c_30])).
% 8.10/2.91  tff(c_10309, plain, (![B_945, A_946]: (v1_funct_2(B_945, k1_relat_1(B_945), A_946) | ~r1_tarski(k2_relat_1(B_945), A_946) | ~v1_funct_1(B_945) | ~v1_relat_1(B_945))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.10/2.91  tff(c_10318, plain, (![A_946]: (v1_funct_2('#skF_3', '#skF_3', A_946) | ~r1_tarski(k2_relat_1('#skF_3'), A_946) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9934, c_10309])).
% 8.10/2.91  tff(c_10321, plain, (![A_946]: (v1_funct_2('#skF_3', '#skF_3', A_946))), inference(demodulation, [status(thm), theory('equality')], [c_5051, c_74, c_9935, c_9933, c_10318])).
% 8.10/2.91  tff(c_9931, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9925, c_9925, c_14])).
% 8.10/2.91  tff(c_9924, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7413])).
% 8.10/2.91  tff(c_9969, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9925, c_9925, c_9924])).
% 8.10/2.91  tff(c_9970, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_9969])).
% 8.10/2.91  tff(c_9972, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9970, c_5002])).
% 8.10/2.91  tff(c_10053, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9931, c_9972])).
% 8.10/2.91  tff(c_5018, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_5003])).
% 8.10/2.91  tff(c_9927, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9925, c_9925, c_5018])).
% 8.10/2.91  tff(c_10062, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_10053, c_9927])).
% 8.10/2.91  tff(c_9974, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9970, c_4997])).
% 8.10/2.91  tff(c_10070, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10062, c_9974])).
% 8.10/2.91  tff(c_10324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10321, c_10070])).
% 8.10/2.91  tff(c_10325, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_9969])).
% 8.10/2.91  tff(c_10326, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_9969])).
% 8.10/2.91  tff(c_10348, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10325, c_10326])).
% 8.10/2.91  tff(c_46, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.10/2.91  tff(c_76, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_46])).
% 8.10/2.91  tff(c_9928, plain, (![A_28]: (v1_funct_2('#skF_3', A_28, '#skF_3') | A_28='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9925, c_9925, c_9925, c_76])).
% 8.10/2.91  tff(c_10521, plain, (![A_957]: (v1_funct_2('#skF_1', A_957, '#skF_1') | A_957='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10325, c_10325, c_10325, c_9928])).
% 8.10/2.91  tff(c_9932, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9925, c_9925, c_12])).
% 8.10/2.91  tff(c_10375, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10325, c_10325, c_9932])).
% 8.10/2.91  tff(c_10336, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10325, c_5002])).
% 8.10/2.92  tff(c_10471, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10375, c_10336])).
% 8.10/2.92  tff(c_10447, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10325, c_10325, c_9927])).
% 8.10/2.92  tff(c_10480, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_10471, c_10447])).
% 8.10/2.92  tff(c_10338, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10325, c_4997])).
% 8.10/2.92  tff(c_10488, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10480, c_10338])).
% 8.10/2.92  tff(c_10524, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_10521, c_10488])).
% 8.10/2.92  tff(c_10528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10348, c_10524])).
% 8.10/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.10/2.92  
% 8.10/2.92  Inference rules
% 8.10/2.92  ----------------------
% 8.10/2.92  #Ref     : 0
% 8.10/2.92  #Sup     : 2148
% 8.10/2.92  #Fact    : 0
% 8.10/2.92  #Define  : 0
% 8.10/2.92  #Split   : 45
% 8.10/2.92  #Chain   : 0
% 8.10/2.92  #Close   : 0
% 8.10/2.92  
% 8.10/2.92  Ordering : KBO
% 8.10/2.92  
% 8.10/2.92  Simplification rules
% 8.10/2.92  ----------------------
% 8.10/2.92  #Subsume      : 284
% 8.10/2.92  #Demod        : 3197
% 8.10/2.92  #Tautology    : 1167
% 8.10/2.92  #SimpNegUnit  : 48
% 8.10/2.92  #BackRed      : 493
% 8.10/2.92  
% 8.10/2.92  #Partial instantiations: 0
% 8.10/2.92  #Strategies tried      : 1
% 8.10/2.92  
% 8.10/2.92  Timing (in seconds)
% 8.10/2.92  ----------------------
% 8.10/2.92  Preprocessing        : 0.46
% 8.10/2.92  Parsing              : 0.20
% 8.10/2.92  CNF conversion       : 0.04
% 8.10/2.92  Main loop            : 1.54
% 8.10/2.92  Inferencing          : 0.53
% 8.10/2.92  Reduction            : 0.54
% 8.10/2.92  Demodulation         : 0.38
% 8.10/2.92  BG Simplification    : 0.07
% 8.10/2.92  Subsumption          : 0.29
% 8.10/2.92  Abstraction          : 0.07
% 8.10/2.92  MUC search           : 0.00
% 8.10/2.92  Cooper               : 0.00
% 8.10/2.92  Total                : 2.14
% 8.10/2.92  Index Insertion      : 0.00
% 8.10/2.92  Index Deletion       : 0.00
% 8.10/2.92  Index Matching       : 0.00
% 8.10/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
