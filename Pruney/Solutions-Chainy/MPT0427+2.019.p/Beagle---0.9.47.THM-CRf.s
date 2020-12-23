%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:58 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 364 expanded)
%              Number of leaves         :   30 ( 129 expanded)
%              Depth                    :    9
%              Number of atoms          :  179 ( 807 expanded)
%              Number of equality atoms :   46 ( 230 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_110,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_122,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_2'(A_47,B_48),B_48)
      | r1_xboole_0(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | r1_xboole_0(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( ~ r1_xboole_0(B_17,A_16)
      | ~ r1_tarski(B_17,A_16)
      | v1_xboole_0(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_137,plain,(
    ! [A_51,B_52] :
      ( ~ r1_tarski(A_51,B_52)
      | v1_xboole_0(A_51)
      | ~ v1_xboole_0(B_52) ) ),
    inference(resolution,[status(thm)],[c_127,c_24])).

tff(c_153,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_137])).

tff(c_154,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_300,plain,(
    ! [A_72,B_73] :
      ( k6_setfam_1(A_72,B_73) = k1_setfam_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(A_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_312,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_300])).

tff(c_443,plain,(
    ! [A_91,B_92] :
      ( k8_setfam_1(A_91,B_92) = k6_setfam_1(A_91,B_92)
      | k1_xboole_0 = B_92
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_454,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_443])).

tff(c_461,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_454])).

tff(c_465,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_20,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_106,plain,(
    ! [B_45,A_46] :
      ( ~ r1_xboole_0(B_45,A_46)
      | ~ r1_tarski(B_45,A_46)
      | v1_xboole_0(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_112,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_106])).

tff(c_116,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_112])).

tff(c_481,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_116])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_313,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_300])).

tff(c_457,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_443])).

tff(c_463,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_457])).

tff(c_560,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_463])).

tff(c_561,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_560])).

tff(c_564,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_154])).

tff(c_575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_564])).

tff(c_576,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_376,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(k8_setfam_1(A_82,B_83),k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_402,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(k8_setfam_1(A_89,B_90),A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(A_89))) ) ),
    inference(resolution,[status(thm)],[c_376,c_34])).

tff(c_416,plain,(
    r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_402])).

tff(c_578,plain,(
    r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_416])).

tff(c_61,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_68,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_61])).

tff(c_36,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_183,plain,(
    ! [A_57] :
      ( k8_setfam_1(A_57,k1_xboole_0) = A_57
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_187,plain,(
    ! [A_57] :
      ( k8_setfam_1(A_57,k1_xboole_0) = A_57
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_36,c_183])).

tff(c_635,plain,(
    ! [A_102] :
      ( k8_setfam_1(A_102,'#skF_4') = A_102
      | ~ r1_tarski('#skF_4',k1_zfmisc_1(A_102)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_465,c_187])).

tff(c_639,plain,(
    k8_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_68,c_635])).

tff(c_40,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_579,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_40])).

tff(c_640,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_579])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_640])).

tff(c_646,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_38,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k1_setfam_1(B_27),k1_setfam_1(A_26))
      | k1_xboole_0 = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_676,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_209,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(C_65,B_64)
      | ~ r2_hidden(C_65,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_222,plain,(
    ! [C_66] : ~ r2_hidden(C_66,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_209])).

tff(c_259,plain,(
    ! [B_68] : r1_xboole_0(k1_xboole_0,B_68) ),
    inference(resolution,[status(thm)],[c_10,c_222])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_xboole_0(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_277,plain,(
    ! [A_69,B_70] :
      ( r1_xboole_0(A_69,B_70)
      | ~ r1_tarski(A_69,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_259,c_18])).

tff(c_359,plain,(
    ! [A_79,B_80,A_81] :
      ( r1_xboole_0(A_79,B_80)
      | ~ r1_tarski(A_79,A_81)
      | ~ r1_tarski(A_81,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_277,c_18])).

tff(c_374,plain,(
    ! [B_80] :
      ( r1_xboole_0('#skF_4',B_80)
      | ~ r1_tarski('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_359])).

tff(c_375,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_682,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_375])).

tff(c_698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_682])).

tff(c_699,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_645,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_648,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_40])).

tff(c_701,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_648])).

tff(c_727,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_701])).

tff(c_730,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_727])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_730])).

tff(c_734,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_157,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_xboole_0(A_53,C_54)
      | ~ r1_xboole_0(B_55,C_54)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_167,plain,(
    ! [A_56] :
      ( r1_xboole_0(A_56,k1_xboole_0)
      | ~ r1_tarski(A_56,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_157])).

tff(c_178,plain,(
    ! [A_56] :
      ( v1_xboole_0(A_56)
      | ~ r1_tarski(A_56,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_167,c_24])).

tff(c_760,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_734,c_178])).

tff(c_776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_760])).

tff(c_777,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_92,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_2'(A_40,B_41),A_40)
      | r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,(
    ! [A_42,B_43] :
      ( ~ v1_xboole_0(A_42)
      | r1_xboole_0(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_22,plain,(
    ! [A_15] :
      ( ~ r1_xboole_0(A_15,A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_102,plain,(
    ! [B_43] :
      ( k1_xboole_0 = B_43
      | ~ v1_xboole_0(B_43) ) ),
    inference(resolution,[status(thm)],[c_97,c_22])).

tff(c_782,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_777,c_102])).

tff(c_778,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_786,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_778,c_102])).

tff(c_796,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_786])).

tff(c_75,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_75])).

tff(c_91,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_799,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_91])).

tff(c_807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_799])).

tff(c_808,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_811,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_40])).

tff(c_817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:25:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.43  
% 2.93/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.93/1.44  
% 2.93/1.44  %Foreground sorts:
% 2.93/1.44  
% 2.93/1.44  
% 2.93/1.44  %Background operators:
% 2.93/1.44  
% 2.93/1.44  
% 2.93/1.44  %Foreground operators:
% 2.93/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.93/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.44  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.93/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.93/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.44  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.93/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.93/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.93/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.93/1.44  
% 2.93/1.46  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.93/1.46  tff(f_120, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.93/1.46  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.93/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.93/1.46  tff(f_81, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.93/1.46  tff(f_100, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.93/1.46  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.93/1.46  tff(f_73, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.93/1.46  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.93/1.46  tff(f_104, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.93/1.46  tff(f_110, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.93/1.46  tff(f_61, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.93/1.46  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.93/1.46  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.93/1.46  tff(c_122, plain, (![A_47, B_48]: (r2_hidden('#skF_2'(A_47, B_48), B_48) | r1_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.93/1.46  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.46  tff(c_127, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | r1_xboole_0(A_50, B_49))), inference(resolution, [status(thm)], [c_122, c_2])).
% 2.93/1.46  tff(c_24, plain, (![B_17, A_16]: (~r1_xboole_0(B_17, A_16) | ~r1_tarski(B_17, A_16) | v1_xboole_0(B_17))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.93/1.46  tff(c_137, plain, (![A_51, B_52]: (~r1_tarski(A_51, B_52) | v1_xboole_0(A_51) | ~v1_xboole_0(B_52))), inference(resolution, [status(thm)], [c_127, c_24])).
% 2.93/1.46  tff(c_153, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_137])).
% 2.93/1.46  tff(c_154, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_153])).
% 2.93/1.46  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.93/1.46  tff(c_300, plain, (![A_72, B_73]: (k6_setfam_1(A_72, B_73)=k1_setfam_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(A_72))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.93/1.46  tff(c_312, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_300])).
% 2.93/1.46  tff(c_443, plain, (![A_91, B_92]: (k8_setfam_1(A_91, B_92)=k6_setfam_1(A_91, B_92) | k1_xboole_0=B_92 | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.93/1.46  tff(c_454, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_443])).
% 2.93/1.46  tff(c_461, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_312, c_454])).
% 2.93/1.46  tff(c_465, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_461])).
% 2.93/1.46  tff(c_20, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.93/1.46  tff(c_106, plain, (![B_45, A_46]: (~r1_xboole_0(B_45, A_46) | ~r1_tarski(B_45, A_46) | v1_xboole_0(B_45))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.93/1.46  tff(c_112, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_106])).
% 2.93/1.46  tff(c_116, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_112])).
% 2.93/1.46  tff(c_481, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_116])).
% 2.93/1.46  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.93/1.46  tff(c_313, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_300])).
% 2.93/1.46  tff(c_457, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_443])).
% 2.93/1.46  tff(c_463, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_313, c_457])).
% 2.93/1.46  tff(c_560, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_465, c_463])).
% 2.93/1.46  tff(c_561, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_560])).
% 2.93/1.46  tff(c_564, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_561, c_154])).
% 2.93/1.46  tff(c_575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_481, c_564])).
% 2.93/1.46  tff(c_576, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_560])).
% 2.93/1.46  tff(c_376, plain, (![A_82, B_83]: (m1_subset_1(k8_setfam_1(A_82, B_83), k1_zfmisc_1(A_82)) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.93/1.46  tff(c_34, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.93/1.46  tff(c_402, plain, (![A_89, B_90]: (r1_tarski(k8_setfam_1(A_89, B_90), A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(A_89))))), inference(resolution, [status(thm)], [c_376, c_34])).
% 2.93/1.46  tff(c_416, plain, (r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_44, c_402])).
% 2.93/1.46  tff(c_578, plain, (r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_576, c_416])).
% 2.93/1.46  tff(c_61, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.93/1.46  tff(c_68, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_61])).
% 2.93/1.46  tff(c_36, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.93/1.46  tff(c_183, plain, (![A_57]: (k8_setfam_1(A_57, k1_xboole_0)=A_57 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.93/1.46  tff(c_187, plain, (![A_57]: (k8_setfam_1(A_57, k1_xboole_0)=A_57 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_36, c_183])).
% 2.93/1.46  tff(c_635, plain, (![A_102]: (k8_setfam_1(A_102, '#skF_4')=A_102 | ~r1_tarski('#skF_4', k1_zfmisc_1(A_102)))), inference(demodulation, [status(thm), theory('equality')], [c_465, c_465, c_187])).
% 2.93/1.46  tff(c_639, plain, (k8_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_68, c_635])).
% 2.93/1.46  tff(c_40, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.93/1.46  tff(c_579, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_576, c_40])).
% 2.93/1.46  tff(c_640, plain, (~r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_639, c_579])).
% 2.93/1.46  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_578, c_640])).
% 2.93/1.46  tff(c_646, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_461])).
% 2.93/1.46  tff(c_38, plain, (![B_27, A_26]: (r1_tarski(k1_setfam_1(B_27), k1_setfam_1(A_26)) | k1_xboole_0=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.93/1.46  tff(c_676, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_463])).
% 2.93/1.46  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.93/1.46  tff(c_209, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(C_65, B_64) | ~r2_hidden(C_65, A_63))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.93/1.46  tff(c_222, plain, (![C_66]: (~r2_hidden(C_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_209])).
% 2.93/1.46  tff(c_259, plain, (![B_68]: (r1_xboole_0(k1_xboole_0, B_68))), inference(resolution, [status(thm)], [c_10, c_222])).
% 2.93/1.46  tff(c_18, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, C_14) | ~r1_xboole_0(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.93/1.46  tff(c_277, plain, (![A_69, B_70]: (r1_xboole_0(A_69, B_70) | ~r1_tarski(A_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_259, c_18])).
% 2.93/1.46  tff(c_359, plain, (![A_79, B_80, A_81]: (r1_xboole_0(A_79, B_80) | ~r1_tarski(A_79, A_81) | ~r1_tarski(A_81, k1_xboole_0))), inference(resolution, [status(thm)], [c_277, c_18])).
% 2.93/1.46  tff(c_374, plain, (![B_80]: (r1_xboole_0('#skF_4', B_80) | ~r1_tarski('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_359])).
% 2.93/1.46  tff(c_375, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_374])).
% 2.93/1.46  tff(c_682, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_676, c_375])).
% 2.93/1.46  tff(c_698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_682])).
% 2.93/1.46  tff(c_699, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_463])).
% 2.93/1.46  tff(c_645, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_461])).
% 2.93/1.46  tff(c_648, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_645, c_40])).
% 2.93/1.46  tff(c_701, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_699, c_648])).
% 2.93/1.46  tff(c_727, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_701])).
% 2.93/1.46  tff(c_730, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_727])).
% 2.93/1.46  tff(c_732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_730])).
% 2.93/1.46  tff(c_734, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_374])).
% 2.93/1.46  tff(c_157, plain, (![A_53, C_54, B_55]: (r1_xboole_0(A_53, C_54) | ~r1_xboole_0(B_55, C_54) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.93/1.46  tff(c_167, plain, (![A_56]: (r1_xboole_0(A_56, k1_xboole_0) | ~r1_tarski(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_157])).
% 2.93/1.46  tff(c_178, plain, (![A_56]: (v1_xboole_0(A_56) | ~r1_tarski(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_167, c_24])).
% 2.93/1.46  tff(c_760, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_734, c_178])).
% 2.93/1.46  tff(c_776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_760])).
% 2.93/1.46  tff(c_777, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_153])).
% 2.93/1.46  tff(c_92, plain, (![A_40, B_41]: (r2_hidden('#skF_2'(A_40, B_41), A_40) | r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.93/1.46  tff(c_97, plain, (![A_42, B_43]: (~v1_xboole_0(A_42) | r1_xboole_0(A_42, B_43))), inference(resolution, [status(thm)], [c_92, c_2])).
% 2.93/1.46  tff(c_22, plain, (![A_15]: (~r1_xboole_0(A_15, A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.93/1.46  tff(c_102, plain, (![B_43]: (k1_xboole_0=B_43 | ~v1_xboole_0(B_43))), inference(resolution, [status(thm)], [c_97, c_22])).
% 2.93/1.46  tff(c_782, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_777, c_102])).
% 2.93/1.46  tff(c_778, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_153])).
% 2.93/1.46  tff(c_786, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_778, c_102])).
% 2.93/1.46  tff(c_796, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_782, c_786])).
% 2.93/1.46  tff(c_75, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.93/1.46  tff(c_90, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_75])).
% 2.93/1.46  tff(c_91, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_90])).
% 2.93/1.46  tff(c_799, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_91])).
% 2.93/1.46  tff(c_807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_799])).
% 2.93/1.46  tff(c_808, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_90])).
% 2.93/1.46  tff(c_811, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_40])).
% 2.93/1.46  tff(c_817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_811])).
% 2.93/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.46  
% 2.93/1.46  Inference rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Ref     : 0
% 2.93/1.46  #Sup     : 155
% 2.93/1.46  #Fact    : 0
% 2.93/1.46  #Define  : 0
% 2.93/1.46  #Split   : 11
% 2.93/1.46  #Chain   : 0
% 2.93/1.46  #Close   : 0
% 2.93/1.46  
% 2.93/1.46  Ordering : KBO
% 2.93/1.46  
% 2.93/1.46  Simplification rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Subsume      : 38
% 2.93/1.46  #Demod        : 119
% 2.93/1.46  #Tautology    : 54
% 2.93/1.46  #SimpNegUnit  : 3
% 2.93/1.46  #BackRed      : 69
% 2.93/1.46  
% 2.93/1.46  #Partial instantiations: 0
% 2.93/1.46  #Strategies tried      : 1
% 2.93/1.46  
% 2.93/1.46  Timing (in seconds)
% 2.93/1.46  ----------------------
% 3.05/1.46  Preprocessing        : 0.31
% 3.05/1.46  Parsing              : 0.16
% 3.05/1.46  CNF conversion       : 0.02
% 3.05/1.46  Main loop            : 0.34
% 3.05/1.46  Inferencing          : 0.11
% 3.05/1.46  Reduction            : 0.11
% 3.05/1.46  Demodulation         : 0.07
% 3.05/1.46  BG Simplification    : 0.02
% 3.05/1.46  Subsumption          : 0.07
% 3.05/1.46  Abstraction          : 0.02
% 3.05/1.46  MUC search           : 0.00
% 3.05/1.46  Cooper               : 0.00
% 3.05/1.46  Total                : 0.69
% 3.05/1.46  Index Insertion      : 0.00
% 3.05/1.46  Index Deletion       : 0.00
% 3.05/1.46  Index Matching       : 0.00
% 3.05/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
