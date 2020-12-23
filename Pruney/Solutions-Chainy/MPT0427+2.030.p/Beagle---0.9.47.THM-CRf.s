%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:00 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 291 expanded)
%              Number of leaves         :   30 ( 106 expanded)
%              Depth                    :   10
%              Number of atoms          :  133 ( 611 expanded)
%              Number of equality atoms :   42 ( 199 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_111,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_60,axiom,(
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

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_2'(A_47,B_48),B_48)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_98])).

tff(c_40,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,(
    ! [C_56,B_57,A_58] :
      ( r2_hidden(C_56,B_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_199,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64),B_65)
      | ~ r1_tarski(A_64,B_65)
      | v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_4,c_147])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_230,plain,(
    ! [B_67,A_68] :
      ( ~ v1_xboole_0(B_67)
      | ~ r1_tarski(A_68,B_67)
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_199,c_2])).

tff(c_255,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_230])).

tff(c_256,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_257,plain,(
    ! [A_69,B_70] :
      ( k6_setfam_1(A_69,B_70) = k1_setfam_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_269,plain,(
    k6_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_257])).

tff(c_353,plain,(
    ! [A_82,B_83] :
      ( k8_setfam_1(A_82,B_83) = k6_setfam_1(A_82,B_83)
      | k1_xboole_0 = B_83
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_364,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k6_setfam_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_353])).

tff(c_371,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_364])).

tff(c_393,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_371])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_270,plain,(
    k6_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_257])).

tff(c_367,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k6_setfam_1('#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_353])).

tff(c_373,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_367])).

tff(c_467,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_373])).

tff(c_468,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_20,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_111,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,B_53)
      | ~ r2_hidden(C_54,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_121,plain,(
    ! [C_55] : ~ r2_hidden(C_55,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_111])).

tff(c_141,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_402,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_141])).

tff(c_474,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_402])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_474])).

tff(c_481,plain,(
    k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_139,plain,(
    ! [B_6] : r1_tarski(k1_xboole_0,B_6) ),
    inference(resolution,[status(thm)],[c_10,c_121])).

tff(c_34,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_182,plain,(
    ! [A_62] :
      ( k8_setfam_1(A_62,k1_xboole_0) = A_62
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_185,plain,(
    ! [A_62] :
      ( k8_setfam_1(A_62,k1_xboole_0) = A_62
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_62)) ) ),
    inference(resolution,[status(thm)],[c_34,c_182])).

tff(c_188,plain,(
    ! [A_62] : k8_setfam_1(A_62,k1_xboole_0) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_185])).

tff(c_398,plain,(
    ! [A_62] : k8_setfam_1(A_62,'#skF_5') = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_188])).

tff(c_38,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k8_setfam_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_509,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_38])).

tff(c_533,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_509])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k8_setfam_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_527,plain,
    ( m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_28])).

tff(c_531,plain,(
    m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_527])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_558,plain,(
    r1_tarski(k1_setfam_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_531,c_32])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_558])).

tff(c_564,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_36,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k1_setfam_1(B_26),k1_setfam_1(A_25))
      | k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_588,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_373])).

tff(c_598,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_141])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_598])).

tff(c_604,plain,(
    k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_373])).

tff(c_563,plain,(
    k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_565,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_38])).

tff(c_606,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_565])).

tff(c_619,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_606])).

tff(c_625,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_619])).

tff(c_627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_564,c_625])).

tff(c_629,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_637,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_629,c_12])).

tff(c_628,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_633,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_628,c_12])).

tff(c_653,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_633])).

tff(c_660,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k8_setfam_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_38])).

tff(c_667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_660])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.54/1.35  
% 2.54/1.35  %Foreground sorts:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Background operators:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Foreground operators:
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.54/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.35  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.54/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.54/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.54/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.35  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.54/1.35  
% 2.74/1.37  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.74/1.37  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.74/1.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.74/1.37  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.74/1.37  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.74/1.37  tff(f_72, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.74/1.37  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.74/1.37  tff(f_95, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.74/1.37  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.74/1.37  tff(f_101, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.74/1.37  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.74/1.37  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.74/1.37  tff(c_98, plain, (![A_47, B_48]: (~r2_hidden('#skF_2'(A_47, B_48), B_48) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.74/1.37  tff(c_103, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_98])).
% 2.74/1.37  tff(c_40, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.74/1.37  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.37  tff(c_147, plain, (![C_56, B_57, A_58]: (r2_hidden(C_56, B_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.74/1.37  tff(c_199, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64), B_65) | ~r1_tarski(A_64, B_65) | v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_4, c_147])).
% 2.74/1.37  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.37  tff(c_230, plain, (![B_67, A_68]: (~v1_xboole_0(B_67) | ~r1_tarski(A_68, B_67) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_199, c_2])).
% 2.74/1.37  tff(c_255, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_230])).
% 2.74/1.37  tff(c_256, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_255])).
% 2.74/1.37  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.74/1.37  tff(c_257, plain, (![A_69, B_70]: (k6_setfam_1(A_69, B_70)=k1_setfam_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.74/1.37  tff(c_269, plain, (k6_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_257])).
% 2.74/1.37  tff(c_353, plain, (![A_82, B_83]: (k8_setfam_1(A_82, B_83)=k6_setfam_1(A_82, B_83) | k1_xboole_0=B_83 | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.74/1.37  tff(c_364, plain, (k8_setfam_1('#skF_4', '#skF_5')=k6_setfam_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_353])).
% 2.74/1.37  tff(c_371, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_269, c_364])).
% 2.74/1.37  tff(c_393, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_371])).
% 2.74/1.37  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.74/1.37  tff(c_270, plain, (k6_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_257])).
% 2.74/1.37  tff(c_367, plain, (k8_setfam_1('#skF_4', '#skF_6')=k6_setfam_1('#skF_4', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_42, c_353])).
% 2.74/1.37  tff(c_373, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_270, c_367])).
% 2.74/1.37  tff(c_467, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_393, c_373])).
% 2.74/1.37  tff(c_468, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_467])).
% 2.74/1.37  tff(c_20, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.74/1.37  tff(c_111, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, B_53) | ~r2_hidden(C_54, A_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.74/1.37  tff(c_121, plain, (![C_55]: (~r2_hidden(C_55, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_111])).
% 2.74/1.37  tff(c_141, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_121])).
% 2.74/1.37  tff(c_402, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_393, c_141])).
% 2.74/1.37  tff(c_474, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_468, c_402])).
% 2.74/1.37  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_256, c_474])).
% 2.74/1.37  tff(c_481, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(splitRight, [status(thm)], [c_467])).
% 2.74/1.37  tff(c_139, plain, (![B_6]: (r1_tarski(k1_xboole_0, B_6))), inference(resolution, [status(thm)], [c_10, c_121])).
% 2.74/1.37  tff(c_34, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.74/1.37  tff(c_182, plain, (![A_62]: (k8_setfam_1(A_62, k1_xboole_0)=A_62 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_62))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.74/1.37  tff(c_185, plain, (![A_62]: (k8_setfam_1(A_62, k1_xboole_0)=A_62 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_62)))), inference(resolution, [status(thm)], [c_34, c_182])).
% 2.74/1.37  tff(c_188, plain, (![A_62]: (k8_setfam_1(A_62, k1_xboole_0)=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_139, c_185])).
% 2.74/1.37  tff(c_398, plain, (![A_62]: (k8_setfam_1(A_62, '#skF_5')=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_393, c_188])).
% 2.74/1.37  tff(c_38, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k8_setfam_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.74/1.37  tff(c_509, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_398, c_38])).
% 2.74/1.37  tff(c_533, plain, (~r1_tarski(k1_setfam_1('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_481, c_509])).
% 2.74/1.37  tff(c_28, plain, (![A_19, B_20]: (m1_subset_1(k8_setfam_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.74/1.37  tff(c_527, plain, (m1_subset_1(k1_setfam_1('#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_481, c_28])).
% 2.74/1.37  tff(c_531, plain, (m1_subset_1(k1_setfam_1('#skF_6'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_527])).
% 2.74/1.37  tff(c_32, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.74/1.37  tff(c_558, plain, (r1_tarski(k1_setfam_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_531, c_32])).
% 2.74/1.37  tff(c_562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_533, c_558])).
% 2.74/1.37  tff(c_564, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_371])).
% 2.74/1.37  tff(c_36, plain, (![B_26, A_25]: (r1_tarski(k1_setfam_1(B_26), k1_setfam_1(A_25)) | k1_xboole_0=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.74/1.37  tff(c_588, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_373])).
% 2.74/1.37  tff(c_598, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_588, c_141])).
% 2.74/1.37  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_256, c_598])).
% 2.74/1.37  tff(c_604, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(splitRight, [status(thm)], [c_373])).
% 2.74/1.37  tff(c_563, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_371])).
% 2.74/1.37  tff(c_565, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k1_setfam_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_563, c_38])).
% 2.74/1.37  tff(c_606, plain, (~r1_tarski(k1_setfam_1('#skF_6'), k1_setfam_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_604, c_565])).
% 2.74/1.37  tff(c_619, plain, (k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_36, c_606])).
% 2.74/1.37  tff(c_625, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_619])).
% 2.74/1.37  tff(c_627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_564, c_625])).
% 2.74/1.37  tff(c_629, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_255])).
% 2.74/1.37  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.74/1.37  tff(c_637, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_629, c_12])).
% 2.74/1.37  tff(c_628, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_255])).
% 2.74/1.37  tff(c_633, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_628, c_12])).
% 2.74/1.37  tff(c_653, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_637, c_633])).
% 2.74/1.37  tff(c_660, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k8_setfam_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_653, c_38])).
% 2.74/1.37  tff(c_667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_660])).
% 2.74/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.37  
% 2.74/1.37  Inference rules
% 2.74/1.37  ----------------------
% 2.74/1.37  #Ref     : 0
% 2.74/1.37  #Sup     : 117
% 2.74/1.37  #Fact    : 0
% 2.74/1.37  #Define  : 0
% 2.74/1.37  #Split   : 6
% 2.74/1.37  #Chain   : 0
% 2.74/1.37  #Close   : 0
% 2.74/1.37  
% 2.74/1.37  Ordering : KBO
% 2.74/1.37  
% 2.74/1.37  Simplification rules
% 2.74/1.37  ----------------------
% 2.74/1.37  #Subsume      : 14
% 2.74/1.37  #Demod        : 95
% 2.74/1.37  #Tautology    : 62
% 2.74/1.37  #SimpNegUnit  : 5
% 2.74/1.37  #BackRed      : 55
% 2.74/1.37  
% 2.74/1.37  #Partial instantiations: 0
% 2.74/1.37  #Strategies tried      : 1
% 2.74/1.37  
% 2.74/1.37  Timing (in seconds)
% 2.74/1.37  ----------------------
% 2.74/1.38  Preprocessing        : 0.31
% 2.74/1.38  Parsing              : 0.17
% 2.74/1.38  CNF conversion       : 0.02
% 2.74/1.38  Main loop            : 0.29
% 2.74/1.38  Inferencing          : 0.10
% 2.74/1.38  Reduction            : 0.09
% 2.74/1.38  Demodulation         : 0.06
% 2.74/1.38  BG Simplification    : 0.02
% 2.74/1.38  Subsumption          : 0.05
% 2.74/1.38  Abstraction          : 0.02
% 2.74/1.38  MUC search           : 0.00
% 2.74/1.38  Cooper               : 0.00
% 2.74/1.38  Total                : 0.64
% 2.74/1.38  Index Insertion      : 0.00
% 2.74/1.38  Index Deletion       : 0.00
% 2.74/1.38  Index Matching       : 0.00
% 2.74/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
