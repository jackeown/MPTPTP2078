%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:56 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 326 expanded)
%              Number of leaves         :   33 ( 121 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 656 expanded)
%              Number of equality atoms :   45 ( 177 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(k1_tarski(A_44),B_45) = B_45
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),B_13) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_98,plain,(
    ! [B_46,A_47] :
      ( k1_xboole_0 != B_46
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_14])).

tff(c_102,plain,(
    ! [A_1] :
      ( k1_xboole_0 != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_36,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_72,plain,(
    ! [B_42,A_43] :
      ( v1_xboole_0(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    ! [A_51,B_52] :
      ( v1_xboole_0(A_51)
      | ~ v1_xboole_0(B_52)
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_30,c_72])).

tff(c_134,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_122])).

tff(c_135,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_139,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_102,c_135])).

tff(c_155,plain,(
    ! [A_57,B_58] :
      ( k6_setfam_1(A_57,B_58) = k1_setfam_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_168,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_155])).

tff(c_213,plain,(
    ! [A_65,B_66] :
      ( k8_setfam_1(A_65,B_66) = k6_setfam_1(A_65,B_66)
      | k1_xboole_0 = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_227,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_213])).

tff(c_233,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_227])).

tff(c_234,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_233])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k8_setfam_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_239,plain,
    ( m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_22])).

tff(c_243,plain,(
    m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_239])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_252,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_243,c_28])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_61,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_50])).

tff(c_167,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_155])).

tff(c_224,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_40,c_213])).

tff(c_231,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_224])).

tff(c_262,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_149,plain,(
    ! [A_55] :
      ( k8_setfam_1(A_55,k1_xboole_0) = A_55
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_153,plain,(
    ! [A_55] :
      ( k8_setfam_1(A_55,k1_xboole_0) = A_55
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_30,c_149])).

tff(c_306,plain,(
    ! [A_73] :
      ( k8_setfam_1(A_73,'#skF_3') = A_73
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_73)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_262,c_153])).

tff(c_310,plain,(
    k8_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_61,c_306])).

tff(c_34,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_235,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_34])).

tff(c_320,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_235])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_320])).

tff(c_325,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_32,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k1_setfam_1(B_28),k1_setfam_1(A_27))
      | k1_xboole_0 = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_324,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_326,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_235])).

tff(c_338,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_326])).

tff(c_341,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_338])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_341])).

tff(c_345,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_353,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_345,c_6])).

tff(c_18,plain,(
    ! [A_17] :
      ( k8_setfam_1(A_17,k1_xboole_0) = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_427,plain,(
    ! [A_83] :
      ( k8_setfam_1(A_83,'#skF_4') = A_83
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_83))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_353,c_18])).

tff(c_435,plain,(
    k8_setfam_1('#skF_2','#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_427])).

tff(c_344,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_349,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_344,c_6])).

tff(c_363,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_349])).

tff(c_370,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_34])).

tff(c_436,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_435,c_370])).

tff(c_479,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1(k8_setfam_1(A_91,B_92),k1_zfmisc_1(A_91))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_492,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_479])).

tff(c_497,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_492])).

tff(c_503,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_497,c_28])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_436,c_503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:32:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.38  
% 2.47/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.47/1.38  
% 2.47/1.38  %Foreground sorts:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Background operators:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Foreground operators:
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.47/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.38  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.47/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.47/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.38  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.38  
% 2.47/1.40  tff(f_94, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.47/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.47/1.40  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.47/1.40  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.47/1.40  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.47/1.40  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.47/1.40  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.47/1.40  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.47/1.40  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.47/1.40  tff(f_84, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.47/1.40  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.47/1.40  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.47/1.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.40  tff(c_86, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), B_45)=B_45 | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.40  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.40  tff(c_98, plain, (![B_46, A_47]: (k1_xboole_0!=B_46 | ~r2_hidden(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_86, c_14])).
% 2.47/1.40  tff(c_102, plain, (![A_1]: (k1_xboole_0!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_98])).
% 2.47/1.40  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.47/1.40  tff(c_30, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.40  tff(c_72, plain, (![B_42, A_43]: (v1_xboole_0(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.40  tff(c_122, plain, (![A_51, B_52]: (v1_xboole_0(A_51) | ~v1_xboole_0(B_52) | ~r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_30, c_72])).
% 2.47/1.40  tff(c_134, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_122])).
% 2.47/1.40  tff(c_135, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_134])).
% 2.47/1.40  tff(c_139, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_102, c_135])).
% 2.47/1.40  tff(c_155, plain, (![A_57, B_58]: (k6_setfam_1(A_57, B_58)=k1_setfam_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.40  tff(c_168, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_155])).
% 2.47/1.40  tff(c_213, plain, (![A_65, B_66]: (k8_setfam_1(A_65, B_66)=k6_setfam_1(A_65, B_66) | k1_xboole_0=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.40  tff(c_227, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_213])).
% 2.47/1.40  tff(c_233, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_227])).
% 2.47/1.40  tff(c_234, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_139, c_233])).
% 2.47/1.40  tff(c_22, plain, (![A_19, B_20]: (m1_subset_1(k8_setfam_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.47/1.40  tff(c_239, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_234, c_22])).
% 2.47/1.40  tff(c_243, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_239])).
% 2.47/1.40  tff(c_28, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.40  tff(c_252, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_243, c_28])).
% 2.47/1.40  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.47/1.40  tff(c_50, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.40  tff(c_61, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_50])).
% 2.47/1.40  tff(c_167, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_155])).
% 2.47/1.40  tff(c_224, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_40, c_213])).
% 2.47/1.40  tff(c_231, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_167, c_224])).
% 2.47/1.40  tff(c_262, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_231])).
% 2.47/1.40  tff(c_149, plain, (![A_55]: (k8_setfam_1(A_55, k1_xboole_0)=A_55 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.40  tff(c_153, plain, (![A_55]: (k8_setfam_1(A_55, k1_xboole_0)=A_55 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_55)))), inference(resolution, [status(thm)], [c_30, c_149])).
% 2.47/1.40  tff(c_306, plain, (![A_73]: (k8_setfam_1(A_73, '#skF_3')=A_73 | ~r1_tarski('#skF_3', k1_zfmisc_1(A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_262, c_153])).
% 2.47/1.40  tff(c_310, plain, (k8_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_61, c_306])).
% 2.47/1.40  tff(c_34, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.47/1.40  tff(c_235, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_34])).
% 2.47/1.40  tff(c_320, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_235])).
% 2.47/1.40  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_252, c_320])).
% 2.47/1.40  tff(c_325, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_231])).
% 2.47/1.40  tff(c_32, plain, (![B_28, A_27]: (r1_tarski(k1_setfam_1(B_28), k1_setfam_1(A_27)) | k1_xboole_0=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.47/1.40  tff(c_324, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_231])).
% 2.47/1.40  tff(c_326, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_235])).
% 2.47/1.40  tff(c_338, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_326])).
% 2.47/1.40  tff(c_341, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_338])).
% 2.47/1.40  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_325, c_341])).
% 2.47/1.40  tff(c_345, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_134])).
% 2.47/1.40  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.40  tff(c_353, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_345, c_6])).
% 2.47/1.40  tff(c_18, plain, (![A_17]: (k8_setfam_1(A_17, k1_xboole_0)=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.40  tff(c_427, plain, (![A_83]: (k8_setfam_1(A_83, '#skF_4')=A_83 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_83))))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_353, c_18])).
% 2.47/1.40  tff(c_435, plain, (k8_setfam_1('#skF_2', '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_38, c_427])).
% 2.47/1.40  tff(c_344, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_134])).
% 2.47/1.40  tff(c_349, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_344, c_6])).
% 2.47/1.40  tff(c_363, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_353, c_349])).
% 2.47/1.40  tff(c_370, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_34])).
% 2.47/1.40  tff(c_436, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_435, c_370])).
% 2.47/1.40  tff(c_479, plain, (![A_91, B_92]: (m1_subset_1(k8_setfam_1(A_91, B_92), k1_zfmisc_1(A_91)) | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.47/1.40  tff(c_492, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_435, c_479])).
% 2.47/1.40  tff(c_497, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_492])).
% 2.47/1.40  tff(c_503, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_497, c_28])).
% 2.47/1.40  tff(c_508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_436, c_503])).
% 2.47/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.40  
% 2.47/1.40  Inference rules
% 2.47/1.40  ----------------------
% 2.47/1.40  #Ref     : 0
% 2.47/1.40  #Sup     : 100
% 2.47/1.40  #Fact    : 0
% 2.47/1.40  #Define  : 0
% 2.47/1.40  #Split   : 4
% 2.47/1.40  #Chain   : 0
% 2.47/1.40  #Close   : 0
% 2.47/1.40  
% 2.47/1.40  Ordering : KBO
% 2.47/1.40  
% 2.47/1.40  Simplification rules
% 2.47/1.40  ----------------------
% 2.47/1.40  #Subsume      : 13
% 2.47/1.40  #Demod        : 54
% 2.47/1.40  #Tautology    : 46
% 2.47/1.40  #SimpNegUnit  : 3
% 2.47/1.40  #BackRed      : 26
% 2.47/1.40  
% 2.47/1.40  #Partial instantiations: 0
% 2.47/1.40  #Strategies tried      : 1
% 2.47/1.40  
% 2.47/1.40  Timing (in seconds)
% 2.47/1.40  ----------------------
% 2.47/1.40  Preprocessing        : 0.30
% 2.47/1.40  Parsing              : 0.16
% 2.47/1.40  CNF conversion       : 0.02
% 2.47/1.40  Main loop            : 0.28
% 2.47/1.40  Inferencing          : 0.10
% 2.47/1.40  Reduction            : 0.09
% 2.47/1.40  Demodulation         : 0.06
% 2.47/1.40  BG Simplification    : 0.02
% 2.47/1.40  Subsumption          : 0.04
% 2.47/1.40  Abstraction          : 0.02
% 2.47/1.40  MUC search           : 0.00
% 2.47/1.40  Cooper               : 0.00
% 2.47/1.40  Total                : 0.61
% 2.47/1.40  Index Insertion      : 0.00
% 2.47/1.40  Index Deletion       : 0.00
% 2.47/1.41  Index Matching       : 0.00
% 2.47/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
