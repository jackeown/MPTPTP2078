%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:02 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 940 expanded)
%              Number of leaves         :   25 ( 312 expanded)
%              Depth                    :   14
%              Number of atoms          :  212 (2108 expanded)
%              Number of equality atoms :   75 ( 735 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_41,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_53,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_438,plain,(
    ! [A_65,B_66] :
      ( k6_setfam_1(A_65,B_66) = k1_setfam_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_450,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_438])).

tff(c_486,plain,(
    ! [A_73,B_74] :
      ( k8_setfam_1(A_73,B_74) = k6_setfam_1(A_73,B_74)
      | k1_xboole_0 = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_497,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_486])).

tff(c_504,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_497])).

tff(c_507,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_504])).

tff(c_451,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_438])).

tff(c_500,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_486])).

tff(c_506,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_500])).

tff(c_526,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_506])).

tff(c_527,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_100,plain,(
    ! [A_38,B_39] :
      ( k6_setfam_1(A_38,B_39) = k1_setfam_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_112,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_100])).

tff(c_165,plain,(
    ! [A_46,B_47] :
      ( k8_setfam_1(A_46,B_47) = k6_setfam_1(A_46,B_47)
      | k1_xboole_0 = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_176,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_165])).

tff(c_183,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_176])).

tff(c_186,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_113,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_100])).

tff(c_179,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_165])).

tff(c_185,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_179])).

tff(c_205,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_185])).

tff(c_206,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_213,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_28])).

tff(c_6,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [B_25,A_26] :
      ( ~ r1_xboole_0(B_25,A_26)
      | ~ r1_tarski(B_25,A_26)
      | v1_xboole_0(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_59,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_197,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_186,c_59])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_206,c_206,c_197])).

tff(c_236,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_122,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k8_setfam_1(A_40,B_41),k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(A_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_143,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k8_setfam_1(A_44,B_45),A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(resolution,[status(thm)],[c_122,c_20])).

tff(c_157,plain,(
    r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_143])).

tff(c_254,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_157])).

tff(c_52,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_64,plain,(
    ! [A_30] :
      ( k8_setfam_1(A_30,k1_xboole_0) = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_68,plain,(
    ! [A_30] :
      ( k8_setfam_1(A_30,k1_xboole_0) = A_30
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_30)) ) ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_284,plain,(
    ! [A_52] :
      ( k8_setfam_1(A_52,'#skF_2') = A_52
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(A_52)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_186,c_68])).

tff(c_288,plain,(
    k8_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_52,c_284])).

tff(c_26,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_255,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_26])).

tff(c_289,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_255])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_289])).

tff(c_295,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_setfam_1(B_17),k1_setfam_1(A_16))
      | k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_315,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_316,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_295])).

tff(c_60,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_xboole_0(A_27,C_28)
      | ~ r1_xboole_0(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_31] :
      ( r1_xboole_0(A_31,k1_xboole_0)
      | ~ r1_tarski(A_31,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ r1_xboole_0(B_7,A_6)
      | ~ r1_tarski(B_7,A_6)
      | v1_xboole_0(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_80,plain,(
    ! [A_31] :
      ( v1_xboole_0(A_31)
      | ~ r1_tarski(A_31,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_69,c_10])).

tff(c_350,plain,(
    ! [A_55] :
      ( v1_xboole_0(A_55)
      | ~ r1_tarski(A_55,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_80])).

tff(c_354,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_350])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_329,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_2])).

tff(c_357,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_354,c_329])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_357])).

tff(c_362,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_294,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_297,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_26])).

tff(c_364,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_297])).

tff(c_377,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_364])).

tff(c_380,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_377])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_380])).

tff(c_384,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_517,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_507,c_384])).

tff(c_546,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_527,c_517])).

tff(c_390,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_xboole_0(A_56,C_57)
      | ~ r1_xboole_0(B_58,C_57)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_399,plain,(
    ! [A_60] :
      ( r1_xboole_0(A_60,k1_xboole_0)
      | ~ r1_tarski(A_60,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_390])).

tff(c_4,plain,(
    ! [A_2,C_4,B_3] :
      ( r1_xboole_0(A_2,C_4)
      | ~ r1_xboole_0(B_3,C_4)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_422,plain,(
    ! [A_63,A_64] :
      ( r1_xboole_0(A_63,k1_xboole_0)
      | ~ r1_tarski(A_63,A_64)
      | ~ r1_tarski(A_64,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_399,c_4])).

tff(c_436,plain,
    ( r1_xboole_0('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_422])).

tff(c_437,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_511,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_437])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_527,c_511])).

tff(c_560,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k8_setfam_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_586,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_16])).

tff(c_590,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_586])).

tff(c_617,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_590,c_20])).

tff(c_394,plain,(
    ! [A_59] :
      ( k8_setfam_1(A_59,k1_xboole_0) = A_59
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_398,plain,(
    ! [A_59] :
      ( k8_setfam_1(A_59,k1_xboole_0) = A_59
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_22,c_394])).

tff(c_618,plain,(
    ! [A_79] :
      ( k8_setfam_1(A_79,'#skF_2') = A_79
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(A_79)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_507,c_398])).

tff(c_622,plain,(
    k8_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_52,c_618])).

tff(c_582,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_26])).

tff(c_623,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_582])).

tff(c_626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_623])).

tff(c_628,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_646,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_657,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_646,c_384])).

tff(c_651,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_437])).

tff(c_682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_651])).

tff(c_683,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_627,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_629,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_26])).

tff(c_685,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_629])).

tff(c_697,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_685])).

tff(c_700,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_697])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_628,c_700])).

tff(c_704,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_410,plain,(
    ! [A_60] :
      ( v1_xboole_0(A_60)
      | ~ r1_tarski(A_60,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_399,c_10])).

tff(c_720,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_704,c_410])).

tff(c_724,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_720,c_2])).

tff(c_850,plain,(
    ! [A_91] :
      ( k8_setfam_1(A_91,'#skF_3') = A_91
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_91)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_724,c_398])).

tff(c_854,plain,(
    k8_setfam_1('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_53,c_850])).

tff(c_703,plain,(
    r1_xboole_0('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_726,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_703])).

tff(c_769,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_726,c_10])).

tff(c_773,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_769])).

tff(c_780,plain,(
    ! [A_83] :
      ( A_83 = '#skF_3'
      | ~ v1_xboole_0(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_2])).

tff(c_787,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_773,c_780])).

tff(c_793,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_26])).

tff(c_855,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_854,c_793])).

tff(c_859,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_16])).

tff(c_863,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_859])).

tff(c_867,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_863,c_20])).

tff(c_871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_855,c_867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.48  
% 2.94/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.48  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.00/1.48  
% 3.00/1.48  %Foreground sorts:
% 3.00/1.48  
% 3.00/1.48  
% 3.00/1.48  %Background operators:
% 3.00/1.48  
% 3.00/1.48  
% 3.00/1.48  %Foreground operators:
% 3.00/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.48  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.00/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.00/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.00/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.00/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.48  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.00/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.00/1.48  
% 3.00/1.50  tff(f_94, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.00/1.50  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.00/1.50  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.00/1.50  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.00/1.50  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.00/1.50  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.00/1.50  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.00/1.50  tff(f_84, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.00/1.50  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.00/1.50  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.00/1.50  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.00/1.50  tff(c_41, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.00/1.50  tff(c_53, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_41])).
% 3.00/1.50  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.00/1.50  tff(c_438, plain, (![A_65, B_66]: (k6_setfam_1(A_65, B_66)=k1_setfam_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.00/1.50  tff(c_450, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_438])).
% 3.00/1.50  tff(c_486, plain, (![A_73, B_74]: (k8_setfam_1(A_73, B_74)=k6_setfam_1(A_73, B_74) | k1_xboole_0=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.50  tff(c_497, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_486])).
% 3.00/1.50  tff(c_504, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_450, c_497])).
% 3.00/1.50  tff(c_507, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_504])).
% 3.00/1.50  tff(c_451, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_438])).
% 3.00/1.50  tff(c_500, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_486])).
% 3.00/1.50  tff(c_506, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_451, c_500])).
% 3.00/1.50  tff(c_526, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_507, c_506])).
% 3.00/1.50  tff(c_527, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_526])).
% 3.00/1.50  tff(c_100, plain, (![A_38, B_39]: (k6_setfam_1(A_38, B_39)=k1_setfam_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(A_38))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.00/1.50  tff(c_112, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_100])).
% 3.00/1.50  tff(c_165, plain, (![A_46, B_47]: (k8_setfam_1(A_46, B_47)=k6_setfam_1(A_46, B_47) | k1_xboole_0=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.50  tff(c_176, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_165])).
% 3.00/1.50  tff(c_183, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_176])).
% 3.00/1.50  tff(c_186, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_183])).
% 3.00/1.50  tff(c_113, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_100])).
% 3.00/1.50  tff(c_179, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_165])).
% 3.00/1.50  tff(c_185, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_179])).
% 3.00/1.50  tff(c_205, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_186, c_185])).
% 3.00/1.50  tff(c_206, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_205])).
% 3.00/1.50  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.00/1.50  tff(c_213, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_28])).
% 3.00/1.50  tff(c_6, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.00/1.50  tff(c_54, plain, (![B_25, A_26]: (~r1_xboole_0(B_25, A_26) | ~r1_tarski(B_25, A_26) | v1_xboole_0(B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.00/1.50  tff(c_58, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_54])).
% 3.00/1.50  tff(c_59, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_58])).
% 3.00/1.50  tff(c_197, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_186, c_59])).
% 3.00/1.50  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_213, c_206, c_206, c_197])).
% 3.00/1.50  tff(c_236, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_205])).
% 3.00/1.50  tff(c_122, plain, (![A_40, B_41]: (m1_subset_1(k8_setfam_1(A_40, B_41), k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(A_40))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.00/1.50  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.00/1.50  tff(c_143, plain, (![A_44, B_45]: (r1_tarski(k8_setfam_1(A_44, B_45), A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(k1_zfmisc_1(A_44))))), inference(resolution, [status(thm)], [c_122, c_20])).
% 3.00/1.50  tff(c_157, plain, (r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_30, c_143])).
% 3.00/1.50  tff(c_254, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_157])).
% 3.00/1.50  tff(c_52, plain, (r1_tarski('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_41])).
% 3.00/1.50  tff(c_22, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.00/1.50  tff(c_64, plain, (![A_30]: (k8_setfam_1(A_30, k1_xboole_0)=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.50  tff(c_68, plain, (![A_30]: (k8_setfam_1(A_30, k1_xboole_0)=A_30 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(resolution, [status(thm)], [c_22, c_64])).
% 3.00/1.50  tff(c_284, plain, (![A_52]: (k8_setfam_1(A_52, '#skF_2')=A_52 | ~r1_tarski('#skF_2', k1_zfmisc_1(A_52)))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_186, c_68])).
% 3.00/1.50  tff(c_288, plain, (k8_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_52, c_284])).
% 3.00/1.50  tff(c_26, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.00/1.50  tff(c_255, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_26])).
% 3.00/1.50  tff(c_289, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_255])).
% 3.00/1.50  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_254, c_289])).
% 3.00/1.50  tff(c_295, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_183])).
% 3.00/1.50  tff(c_24, plain, (![B_17, A_16]: (r1_tarski(k1_setfam_1(B_17), k1_setfam_1(A_16)) | k1_xboole_0=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.00/1.50  tff(c_315, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_185])).
% 3.00/1.50  tff(c_316, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_315, c_295])).
% 3.00/1.50  tff(c_60, plain, (![A_27, C_28, B_29]: (r1_xboole_0(A_27, C_28) | ~r1_xboole_0(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.50  tff(c_69, plain, (![A_31]: (r1_xboole_0(A_31, k1_xboole_0) | ~r1_tarski(A_31, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_60])).
% 3.00/1.50  tff(c_10, plain, (![B_7, A_6]: (~r1_xboole_0(B_7, A_6) | ~r1_tarski(B_7, A_6) | v1_xboole_0(B_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.00/1.50  tff(c_80, plain, (![A_31]: (v1_xboole_0(A_31) | ~r1_tarski(A_31, k1_xboole_0))), inference(resolution, [status(thm)], [c_69, c_10])).
% 3.00/1.50  tff(c_350, plain, (![A_55]: (v1_xboole_0(A_55) | ~r1_tarski(A_55, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_80])).
% 3.00/1.50  tff(c_354, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_350])).
% 3.00/1.50  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.00/1.50  tff(c_329, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_2])).
% 3.00/1.50  tff(c_357, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_354, c_329])).
% 3.00/1.50  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_357])).
% 3.00/1.50  tff(c_362, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_185])).
% 3.00/1.50  tff(c_294, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_183])).
% 3.00/1.50  tff(c_297, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_294, c_26])).
% 3.00/1.50  tff(c_364, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_297])).
% 3.00/1.50  tff(c_377, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_364])).
% 3.00/1.50  tff(c_380, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_377])).
% 3.00/1.50  tff(c_382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_380])).
% 3.00/1.50  tff(c_384, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_58])).
% 3.00/1.50  tff(c_517, plain, (r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_507, c_507, c_384])).
% 3.00/1.50  tff(c_546, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_527, c_527, c_517])).
% 3.00/1.50  tff(c_390, plain, (![A_56, C_57, B_58]: (r1_xboole_0(A_56, C_57) | ~r1_xboole_0(B_58, C_57) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.50  tff(c_399, plain, (![A_60]: (r1_xboole_0(A_60, k1_xboole_0) | ~r1_tarski(A_60, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_390])).
% 3.00/1.50  tff(c_4, plain, (![A_2, C_4, B_3]: (r1_xboole_0(A_2, C_4) | ~r1_xboole_0(B_3, C_4) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.50  tff(c_422, plain, (![A_63, A_64]: (r1_xboole_0(A_63, k1_xboole_0) | ~r1_tarski(A_63, A_64) | ~r1_tarski(A_64, k1_xboole_0))), inference(resolution, [status(thm)], [c_399, c_4])).
% 3.00/1.50  tff(c_436, plain, (r1_xboole_0('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_422])).
% 3.00/1.50  tff(c_437, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_436])).
% 3.00/1.50  tff(c_511, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_507, c_437])).
% 3.00/1.50  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_546, c_527, c_511])).
% 3.00/1.50  tff(c_560, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_526])).
% 3.00/1.50  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(k8_setfam_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(k1_zfmisc_1(A_10))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.00/1.50  tff(c_586, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_560, c_16])).
% 3.00/1.50  tff(c_590, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_586])).
% 3.00/1.50  tff(c_617, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_590, c_20])).
% 3.00/1.50  tff(c_394, plain, (![A_59]: (k8_setfam_1(A_59, k1_xboole_0)=A_59 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.50  tff(c_398, plain, (![A_59]: (k8_setfam_1(A_59, k1_xboole_0)=A_59 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_59)))), inference(resolution, [status(thm)], [c_22, c_394])).
% 3.00/1.50  tff(c_618, plain, (![A_79]: (k8_setfam_1(A_79, '#skF_2')=A_79 | ~r1_tarski('#skF_2', k1_zfmisc_1(A_79)))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_507, c_398])).
% 3.00/1.50  tff(c_622, plain, (k8_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_52, c_618])).
% 3.00/1.50  tff(c_582, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_26])).
% 3.00/1.50  tff(c_623, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_582])).
% 3.00/1.50  tff(c_626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_617, c_623])).
% 3.00/1.50  tff(c_628, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_504])).
% 3.00/1.50  tff(c_646, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_506])).
% 3.00/1.50  tff(c_657, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_646, c_646, c_384])).
% 3.00/1.50  tff(c_651, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_646, c_437])).
% 3.00/1.50  tff(c_682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_657, c_651])).
% 3.00/1.50  tff(c_683, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_506])).
% 3.00/1.50  tff(c_627, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_504])).
% 3.00/1.50  tff(c_629, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_627, c_26])).
% 3.00/1.50  tff(c_685, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_629])).
% 3.00/1.50  tff(c_697, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_685])).
% 3.00/1.50  tff(c_700, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_697])).
% 3.00/1.50  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_628, c_700])).
% 3.00/1.50  tff(c_704, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_436])).
% 3.00/1.50  tff(c_410, plain, (![A_60]: (v1_xboole_0(A_60) | ~r1_tarski(A_60, k1_xboole_0))), inference(resolution, [status(thm)], [c_399, c_10])).
% 3.00/1.50  tff(c_720, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_704, c_410])).
% 3.00/1.50  tff(c_724, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_720, c_2])).
% 3.00/1.50  tff(c_850, plain, (![A_91]: (k8_setfam_1(A_91, '#skF_3')=A_91 | ~r1_tarski('#skF_3', k1_zfmisc_1(A_91)))), inference(demodulation, [status(thm), theory('equality')], [c_724, c_724, c_398])).
% 3.00/1.50  tff(c_854, plain, (k8_setfam_1('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_53, c_850])).
% 3.00/1.50  tff(c_703, plain, (r1_xboole_0('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_436])).
% 3.00/1.50  tff(c_726, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_724, c_703])).
% 3.00/1.50  tff(c_769, plain, (~r1_tarski('#skF_2', '#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_726, c_10])).
% 3.00/1.50  tff(c_773, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_769])).
% 3.00/1.50  tff(c_780, plain, (![A_83]: (A_83='#skF_3' | ~v1_xboole_0(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_724, c_2])).
% 3.00/1.50  tff(c_787, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_773, c_780])).
% 3.00/1.50  tff(c_793, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_26])).
% 3.00/1.50  tff(c_855, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_854, c_854, c_793])).
% 3.00/1.50  tff(c_859, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_854, c_16])).
% 3.00/1.50  tff(c_863, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_859])).
% 3.00/1.50  tff(c_867, plain, (r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_863, c_20])).
% 3.00/1.50  tff(c_871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_855, c_867])).
% 3.00/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.50  
% 3.00/1.50  Inference rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Ref     : 0
% 3.00/1.50  #Sup     : 164
% 3.00/1.50  #Fact    : 0
% 3.00/1.50  #Define  : 0
% 3.00/1.50  #Split   : 13
% 3.00/1.50  #Chain   : 0
% 3.00/1.50  #Close   : 0
% 3.00/1.50  
% 3.00/1.50  Ordering : KBO
% 3.00/1.50  
% 3.00/1.50  Simplification rules
% 3.00/1.50  ----------------------
% 3.00/1.50  #Subsume      : 18
% 3.00/1.50  #Demod        : 222
% 3.00/1.50  #Tautology    : 90
% 3.00/1.50  #SimpNegUnit  : 4
% 3.00/1.50  #BackRed      : 103
% 3.00/1.50  
% 3.00/1.50  #Partial instantiations: 0
% 3.00/1.50  #Strategies tried      : 1
% 3.00/1.50  
% 3.00/1.50  Timing (in seconds)
% 3.00/1.50  ----------------------
% 3.00/1.51  Preprocessing        : 0.34
% 3.00/1.51  Parsing              : 0.18
% 3.00/1.51  CNF conversion       : 0.02
% 3.00/1.51  Main loop            : 0.37
% 3.00/1.51  Inferencing          : 0.13
% 3.00/1.51  Reduction            : 0.12
% 3.00/1.51  Demodulation         : 0.08
% 3.00/1.51  BG Simplification    : 0.02
% 3.00/1.51  Subsumption          : 0.07
% 3.00/1.51  Abstraction          : 0.02
% 3.00/1.51  MUC search           : 0.00
% 3.00/1.51  Cooper               : 0.00
% 3.00/1.51  Total                : 0.76
% 3.00/1.51  Index Insertion      : 0.00
% 3.00/1.51  Index Deletion       : 0.00
% 3.00/1.51  Index Matching       : 0.00
% 3.00/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
