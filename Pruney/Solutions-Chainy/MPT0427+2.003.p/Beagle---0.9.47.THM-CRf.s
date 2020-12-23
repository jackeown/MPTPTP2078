%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:56 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 297 expanded)
%              Number of leaves         :   26 ( 105 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 624 expanded)
%              Number of equality atoms :   46 ( 222 expanded)
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

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_62,plain,(
    ! [B_28,A_29] :
      ( v1_xboole_0(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_29))
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_94,plain,(
    ! [A_32,B_33] :
      ( v1_xboole_0(A_32)
      | ~ v1_xboole_0(B_33)
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_28,c_62])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_94])).

tff(c_111,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_130,plain,(
    ! [A_37,B_38] :
      ( k6_setfam_1(A_37,B_38) = k1_setfam_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(A_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_142,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_130])).

tff(c_244,plain,(
    ! [A_51,B_52] :
      ( k8_setfam_1(A_51,B_52) = k6_setfam_1(A_51,B_52)
      | k1_xboole_0 = B_52
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_255,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_244])).

tff(c_262,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_255])).

tff(c_265,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_143,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_130])).

tff(c_258,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_244])).

tff(c_264,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_258])).

tff(c_278,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_264])).

tff(c_279,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_10,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [B_34,A_35] :
      ( ~ r1_xboole_0(B_34,A_35)
      | ~ r1_tarski(B_34,A_35)
      | v1_xboole_0(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_116,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_119,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_116])).

tff(c_270,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_119])).

tff(c_280,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_270])).

tff(c_292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_280])).

tff(c_293,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_186,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k8_setfam_1(A_45,B_46),k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_200,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k8_setfam_1(A_47,B_48),A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(resolution,[status(thm)],[c_186,c_26])).

tff(c_214,plain,(
    r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_200])).

tff(c_313,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_214])).

tff(c_49,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_125,plain,(
    ! [A_36] :
      ( k8_setfam_1(A_36,k1_xboole_0) = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_129,plain,(
    ! [A_36] :
      ( k8_setfam_1(A_36,k1_xboole_0) = A_36
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_36)) ) ),
    inference(resolution,[status(thm)],[c_28,c_125])).

tff(c_347,plain,(
    ! [A_55] :
      ( k8_setfam_1(A_55,'#skF_2') = A_55
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(A_55)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_265,c_129])).

tff(c_351,plain,(
    k8_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_347])).

tff(c_32,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_314,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_32])).

tff(c_361,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_314])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_361])).

tff(c_368,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_setfam_1(B_19),k1_setfam_1(A_18))
      | k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_403,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_409,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_119])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_409])).

tff(c_415,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_367,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_371,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_32])).

tff(c_417,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_371])).

tff(c_442,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_417])).

tff(c_445,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_442])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_445])).

tff(c_449,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_457,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_449,c_2])).

tff(c_448,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_453,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_448,c_2])).

tff(c_465,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_453])).

tff(c_76,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_76])).

tff(c_92,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_472,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_92])).

tff(c_480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_472])).

tff(c_481,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_491,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_32])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  
% 2.16/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.16/1.32  
% 2.16/1.32  %Foreground sorts:
% 2.16/1.32  
% 2.16/1.32  
% 2.16/1.32  %Background operators:
% 2.16/1.32  
% 2.16/1.32  
% 2.16/1.32  %Foreground operators:
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.32  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.16/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.32  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.32  
% 2.61/1.34  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.34  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.61/1.34  tff(f_85, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.61/1.34  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.61/1.34  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.61/1.34  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.61/1.34  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.61/1.34  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.61/1.34  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.61/1.34  tff(f_91, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.61/1.34  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.61/1.34  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.34  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.61/1.34  tff(c_28, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.61/1.34  tff(c_62, plain, (![B_28, A_29]: (v1_xboole_0(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_29)) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.61/1.34  tff(c_94, plain, (![A_32, B_33]: (v1_xboole_0(A_32) | ~v1_xboole_0(B_33) | ~r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_28, c_62])).
% 2.61/1.34  tff(c_110, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_94])).
% 2.61/1.34  tff(c_111, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_110])).
% 2.61/1.34  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.61/1.34  tff(c_130, plain, (![A_37, B_38]: (k6_setfam_1(A_37, B_38)=k1_setfam_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(k1_zfmisc_1(A_37))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.61/1.34  tff(c_142, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_130])).
% 2.61/1.34  tff(c_244, plain, (![A_51, B_52]: (k8_setfam_1(A_51, B_52)=k6_setfam_1(A_51, B_52) | k1_xboole_0=B_52 | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.61/1.34  tff(c_255, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_244])).
% 2.61/1.34  tff(c_262, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_255])).
% 2.61/1.34  tff(c_265, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_262])).
% 2.61/1.34  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.61/1.34  tff(c_143, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_130])).
% 2.61/1.34  tff(c_258, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_244])).
% 2.61/1.34  tff(c_264, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_258])).
% 2.61/1.34  tff(c_278, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_265, c_264])).
% 2.61/1.34  tff(c_279, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_278])).
% 2.61/1.34  tff(c_10, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.34  tff(c_113, plain, (![B_34, A_35]: (~r1_xboole_0(B_34, A_35) | ~r1_tarski(B_34, A_35) | v1_xboole_0(B_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.34  tff(c_116, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_113])).
% 2.61/1.34  tff(c_119, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_116])).
% 2.61/1.34  tff(c_270, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_119])).
% 2.61/1.34  tff(c_280, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_270])).
% 2.61/1.34  tff(c_292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_280])).
% 2.61/1.34  tff(c_293, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_278])).
% 2.61/1.34  tff(c_186, plain, (![A_45, B_46]: (m1_subset_1(k8_setfam_1(A_45, B_46), k1_zfmisc_1(A_45)) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.34  tff(c_26, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.61/1.34  tff(c_200, plain, (![A_47, B_48]: (r1_tarski(k8_setfam_1(A_47, B_48), A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(resolution, [status(thm)], [c_186, c_26])).
% 2.61/1.34  tff(c_214, plain, (r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_36, c_200])).
% 2.61/1.34  tff(c_313, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_214])).
% 2.61/1.34  tff(c_49, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.61/1.34  tff(c_60, plain, (r1_tarski('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_49])).
% 2.61/1.34  tff(c_125, plain, (![A_36]: (k8_setfam_1(A_36, k1_xboole_0)=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.61/1.34  tff(c_129, plain, (![A_36]: (k8_setfam_1(A_36, k1_xboole_0)=A_36 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_36)))), inference(resolution, [status(thm)], [c_28, c_125])).
% 2.61/1.34  tff(c_347, plain, (![A_55]: (k8_setfam_1(A_55, '#skF_2')=A_55 | ~r1_tarski('#skF_2', k1_zfmisc_1(A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_265, c_129])).
% 2.61/1.34  tff(c_351, plain, (k8_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_60, c_347])).
% 2.61/1.34  tff(c_32, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.61/1.34  tff(c_314, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_32])).
% 2.61/1.34  tff(c_361, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_351, c_314])).
% 2.61/1.34  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_313, c_361])).
% 2.61/1.34  tff(c_368, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_262])).
% 2.61/1.34  tff(c_30, plain, (![B_19, A_18]: (r1_tarski(k1_setfam_1(B_19), k1_setfam_1(A_18)) | k1_xboole_0=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.61/1.34  tff(c_403, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_264])).
% 2.61/1.34  tff(c_409, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_119])).
% 2.61/1.34  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_409])).
% 2.61/1.34  tff(c_415, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_264])).
% 2.61/1.34  tff(c_367, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_262])).
% 2.61/1.34  tff(c_371, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_32])).
% 2.61/1.34  tff(c_417, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_371])).
% 2.61/1.34  tff(c_442, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_417])).
% 2.61/1.34  tff(c_445, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_442])).
% 2.61/1.34  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_368, c_445])).
% 2.61/1.34  tff(c_449, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_110])).
% 2.61/1.34  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.34  tff(c_457, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_449, c_2])).
% 2.61/1.34  tff(c_448, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 2.61/1.34  tff(c_453, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_448, c_2])).
% 2.61/1.34  tff(c_465, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_453])).
% 2.61/1.34  tff(c_76, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.34  tff(c_91, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_76])).
% 2.61/1.34  tff(c_92, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_91])).
% 2.61/1.34  tff(c_472, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_92])).
% 2.61/1.34  tff(c_480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_472])).
% 2.61/1.34  tff(c_481, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_91])).
% 2.61/1.34  tff(c_491, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_32])).
% 2.61/1.34  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_491])).
% 2.61/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.34  
% 2.61/1.34  Inference rules
% 2.61/1.34  ----------------------
% 2.61/1.34  #Ref     : 0
% 2.61/1.34  #Sup     : 88
% 2.61/1.34  #Fact    : 0
% 2.61/1.34  #Define  : 0
% 2.61/1.34  #Split   : 11
% 2.61/1.34  #Chain   : 0
% 2.61/1.34  #Close   : 0
% 2.61/1.34  
% 2.61/1.34  Ordering : KBO
% 2.61/1.34  
% 2.61/1.34  Simplification rules
% 2.61/1.34  ----------------------
% 2.61/1.34  #Subsume      : 10
% 2.61/1.34  #Demod        : 88
% 2.61/1.34  #Tautology    : 35
% 2.61/1.34  #SimpNegUnit  : 3
% 2.61/1.34  #BackRed      : 53
% 2.61/1.34  
% 2.61/1.34  #Partial instantiations: 0
% 2.61/1.34  #Strategies tried      : 1
% 2.61/1.34  
% 2.61/1.34  Timing (in seconds)
% 2.61/1.34  ----------------------
% 2.61/1.34  Preprocessing        : 0.31
% 2.61/1.34  Parsing              : 0.17
% 2.61/1.34  CNF conversion       : 0.02
% 2.61/1.34  Main loop            : 0.27
% 2.61/1.34  Inferencing          : 0.09
% 2.61/1.34  Reduction            : 0.09
% 2.61/1.34  Demodulation         : 0.06
% 2.61/1.34  BG Simplification    : 0.01
% 2.61/1.34  Subsumption          : 0.05
% 2.61/1.34  Abstraction          : 0.02
% 2.61/1.34  MUC search           : 0.00
% 2.61/1.34  Cooper               : 0.00
% 2.61/1.34  Total                : 0.61
% 2.61/1.34  Index Insertion      : 0.00
% 2.61/1.34  Index Deletion       : 0.00
% 2.61/1.34  Index Matching       : 0.00
% 2.61/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
