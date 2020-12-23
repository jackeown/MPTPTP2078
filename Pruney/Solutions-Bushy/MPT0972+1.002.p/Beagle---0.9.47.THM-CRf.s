%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0972+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:10 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  107 (1941 expanded)
%              Number of leaves         :   26 ( 687 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 (7478 expanded)
%              Number of equality atoms :   90 (2629 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
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

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(c_30,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_70,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( r2_relset_1(A_39,B_40,C_41,C_41)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    ! [C_43] :
      ( r2_relset_1('#skF_2','#skF_3',C_43,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_83,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_39,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_57,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_50])).

tff(c_84,plain,(
    ! [B_44,A_45,C_46] :
      ( k1_xboole_0 = B_44
      | k1_relset_1(A_45,B_44,C_46) = A_45
      | ~ v1_funct_2(C_46,A_45,B_44)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_84])).

tff(c_93,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_57,c_87])).

tff(c_97,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_47,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_39])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_58,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_90,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_84])).

tff(c_96,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58,c_90])).

tff(c_114,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_128,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_1'(A_50,B_51),k1_relat_1(A_50))
      | B_51 = A_50
      | k1_relat_1(B_51) != k1_relat_1(A_50)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_131,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_1'('#skF_4',B_51),'#skF_2')
      | B_51 = '#skF_4'
      | k1_relat_1(B_51) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_128])).

tff(c_139,plain,(
    ! [B_52] :
      ( r2_hidden('#skF_1'('#skF_4',B_52),'#skF_2')
      | B_52 = '#skF_4'
      | k1_relat_1(B_52) != '#skF_2'
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_38,c_114,c_131])).

tff(c_26,plain,(
    ! [E_24] :
      ( k1_funct_1('#skF_5',E_24) = k1_funct_1('#skF_4',E_24)
      | ~ r2_hidden(E_24,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_143,plain,(
    ! [B_52] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_52)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_52))
      | B_52 = '#skF_4'
      | k1_relat_1(B_52) != '#skF_2'
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_139,c_26])).

tff(c_163,plain,(
    ! [B_55,A_56] :
      ( k1_funct_1(B_55,'#skF_1'(A_56,B_55)) != k1_funct_1(A_56,'#skF_1'(A_56,B_55))
      | B_55 = A_56
      | k1_relat_1(B_55) != k1_relat_1(A_56)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_167,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_163])).

tff(c_170,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_32,c_97,c_47,c_38,c_114,c_97,c_167])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_179,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_24])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_179])).

tff(c_191,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_190,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_6,plain,(
    ! [C_6,A_4] :
      ( k1_xboole_0 = C_6
      | ~ v1_funct_2(C_6,A_4,k1_xboole_0)
      | k1_xboole_0 = A_4
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_207,plain,(
    ! [C_58,A_59] :
      ( C_58 = '#skF_3'
      | ~ v1_funct_2(C_58,A_59,'#skF_3')
      | A_59 = '#skF_3'
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_190,c_190,c_190,c_6])).

tff(c_210,plain,
    ( '#skF_5' = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_207])).

tff(c_216,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_210])).

tff(c_220,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_222,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_191])).

tff(c_233,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_36])).

tff(c_227,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_58])).

tff(c_230,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_34])).

tff(c_12,plain,(
    ! [B_5,C_6] :
      ( k1_relset_1(k1_xboole_0,B_5,C_6) = k1_xboole_0
      | ~ v1_funct_2(C_6,k1_xboole_0,B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_330,plain,(
    ! [B_69,C_70] :
      ( k1_relset_1('#skF_3',B_69,C_70) = '#skF_3'
      | ~ v1_funct_2(C_70,'#skF_3',B_69)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_69))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_190,c_190,c_190,c_12])).

tff(c_336,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_230,c_330])).

tff(c_342,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_227,c_336])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_342])).

tff(c_346,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_213,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_207])).

tff(c_219,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_213])).

tff(c_364,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_219])).

tff(c_345,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_348,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_97])).

tff(c_365,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_348])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_365])).

tff(c_381,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_407,plain,(
    ! [C_75,A_76] :
      ( C_75 = '#skF_3'
      | ~ v1_funct_2(C_75,A_76,'#skF_3')
      | A_76 = '#skF_3'
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_381,c_381,c_381,c_6])).

tff(c_410,plain,
    ( '#skF_5' = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_407])).

tff(c_416,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_410])).

tff(c_420,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_382,plain,(
    k1_relat_1('#skF_5') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_421,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_382])).

tff(c_431,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_30])).

tff(c_426,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_57])).

tff(c_428,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_28])).

tff(c_525,plain,(
    ! [B_85,C_86] :
      ( k1_relset_1('#skF_3',B_85,C_86) = '#skF_3'
      | ~ v1_funct_2(C_86,'#skF_3',B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_85))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_381,c_381,c_381,c_12])).

tff(c_528,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_428,c_525])).

tff(c_534,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_426,c_528])).

tff(c_536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_534])).

tff(c_538,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_413,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_407])).

tff(c_419,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_413])).

tff(c_553,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_538,c_419])).

tff(c_537,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_82,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_540,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_537,c_82])).

tff(c_590,plain,(
    r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_553,c_553,c_540])).

tff(c_545,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_24])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_553,c_553,c_545])).

%------------------------------------------------------------------------------
