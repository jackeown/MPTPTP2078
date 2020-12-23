%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:01 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 254 expanded)
%              Number of leaves         :   28 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 538 expanded)
%              Number of equality atoms :   44 ( 225 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_50,axiom,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_65,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_1'(A_37,B_38),A_37)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [A_37] : r1_tarski(A_37,A_37) ),
    inference(resolution,[status(thm)],[c_65,c_4])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_151,plain,(
    ! [A_53,B_54] :
      ( k6_setfam_1(A_53,B_54) = k1_setfam_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_163,plain,(
    k6_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_151])).

tff(c_246,plain,(
    ! [A_66,B_67] :
      ( k8_setfam_1(A_66,B_67) = k6_setfam_1(A_66,B_67)
      | k1_xboole_0 = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_257,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k6_setfam_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_246])).

tff(c_264,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_257])).

tff(c_267,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_164,plain,(
    k6_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_151])).

tff(c_260,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k6_setfam_1('#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38,c_246])).

tff(c_266,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_260])).

tff(c_300,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_266])).

tff(c_301,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_34,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k8_setfam_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_305,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k8_setfam_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_34])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_305])).

tff(c_313,plain,(
    k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k8_setfam_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_351,plain,
    ( m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_24])).

tff(c_355,plain,(
    m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_351])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_385,plain,(
    r1_tarski(k1_setfam_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_355,c_28])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_78,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,B_43)
      | ~ r2_hidden(C_44,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_95,plain,(
    ! [C_48] : ~ r2_hidden(C_48,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_78])).

tff(c_112,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_71,plain,(
    ! [A_39] :
      ( k8_setfam_1(A_39,k1_xboole_0) = A_39
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_75,plain,(
    ! [A_39] :
      ( k8_setfam_1(A_39,k1_xboole_0) = A_39
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_30,c_71])).

tff(c_118,plain,(
    ! [A_39] : k8_setfam_1(A_39,k1_xboole_0) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_75])).

tff(c_273,plain,(
    ! [A_39] : k8_setfam_1(A_39,'#skF_5') = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_118])).

tff(c_347,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),k8_setfam_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_34])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_273,c_347])).

tff(c_397,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_36,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_setfam_1(B_23),k1_setfam_1(A_22))
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_412,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_413,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_397])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_82,plain,(
    ! [C_45,B_46,A_47] :
      ( r2_hidden(C_45,B_46)
      | ~ r2_hidden(C_45,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_211,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_3'(A_61),B_62)
      | ~ r1_tarski(A_61,B_62)
      | k1_xboole_0 = A_61 ) ),
    inference(resolution,[status(thm)],[c_14,c_82])).

tff(c_81,plain,(
    ! [C_44] : ~ r2_hidden(C_44,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_78])).

tff(c_218,plain,(
    ! [A_61] :
      ( ~ r1_tarski(A_61,k1_xboole_0)
      | k1_xboole_0 = A_61 ) ),
    inference(resolution,[status(thm)],[c_211,c_81])).

tff(c_490,plain,(
    ! [A_82] :
      ( ~ r1_tarski(A_82,'#skF_6')
      | A_82 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_412,c_218])).

tff(c_501,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_36,c_490])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_501])).

tff(c_510,plain,(
    k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_396,plain,(
    k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_398,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_34])).

tff(c_512,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_398])).

tff(c_524,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_512])).

tff(c_527,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_524])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.32  % Computer   : n025.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 18:14:50 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.32  
% 2.53/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.53/1.32  
% 2.53/1.32  %Foreground sorts:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Background operators:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Foreground operators:
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.32  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.53/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.53/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.53/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.32  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.53/1.32  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.53/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.53/1.32  
% 2.53/1.34  tff(f_109, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.53/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.53/1.34  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.53/1.34  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.53/1.34  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.53/1.34  tff(f_93, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.53/1.34  tff(f_70, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.53/1.34  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.53/1.34  tff(f_99, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.53/1.34  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.53/1.34  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.53/1.34  tff(c_65, plain, (![A_37, B_38]: (r2_hidden('#skF_1'(A_37, B_38), A_37) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.34  tff(c_70, plain, (![A_37]: (r1_tarski(A_37, A_37))), inference(resolution, [status(thm)], [c_65, c_4])).
% 2.53/1.34  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.53/1.34  tff(c_151, plain, (![A_53, B_54]: (k6_setfam_1(A_53, B_54)=k1_setfam_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.53/1.34  tff(c_163, plain, (k6_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_151])).
% 2.53/1.34  tff(c_246, plain, (![A_66, B_67]: (k8_setfam_1(A_66, B_67)=k6_setfam_1(A_66, B_67) | k1_xboole_0=B_67 | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.53/1.34  tff(c_257, plain, (k8_setfam_1('#skF_4', '#skF_5')=k6_setfam_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_40, c_246])).
% 2.53/1.34  tff(c_264, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_257])).
% 2.53/1.34  tff(c_267, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_264])).
% 2.53/1.34  tff(c_164, plain, (k6_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_151])).
% 2.53/1.34  tff(c_260, plain, (k8_setfam_1('#skF_4', '#skF_6')=k6_setfam_1('#skF_4', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_38, c_246])).
% 2.53/1.34  tff(c_266, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_260])).
% 2.53/1.34  tff(c_300, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_267, c_266])).
% 2.53/1.34  tff(c_301, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_300])).
% 2.53/1.34  tff(c_34, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k8_setfam_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.53/1.34  tff(c_305, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k8_setfam_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_34])).
% 2.53/1.34  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_305])).
% 2.53/1.34  tff(c_313, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(splitRight, [status(thm)], [c_300])).
% 2.53/1.34  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(k8_setfam_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.53/1.34  tff(c_351, plain, (m1_subset_1(k1_setfam_1('#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_313, c_24])).
% 2.53/1.34  tff(c_355, plain, (m1_subset_1(k1_setfam_1('#skF_6'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_351])).
% 2.53/1.34  tff(c_28, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.53/1.34  tff(c_385, plain, (r1_tarski(k1_setfam_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_355, c_28])).
% 2.53/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.34  tff(c_16, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.53/1.34  tff(c_78, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, B_43) | ~r2_hidden(C_44, A_42))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.53/1.34  tff(c_95, plain, (![C_48]: (~r2_hidden(C_48, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_78])).
% 2.53/1.34  tff(c_112, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_95])).
% 2.53/1.34  tff(c_30, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.53/1.34  tff(c_71, plain, (![A_39]: (k8_setfam_1(A_39, k1_xboole_0)=A_39 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_39))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.53/1.34  tff(c_75, plain, (![A_39]: (k8_setfam_1(A_39, k1_xboole_0)=A_39 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_39)))), inference(resolution, [status(thm)], [c_30, c_71])).
% 2.53/1.34  tff(c_118, plain, (![A_39]: (k8_setfam_1(A_39, k1_xboole_0)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_75])).
% 2.53/1.34  tff(c_273, plain, (![A_39]: (k8_setfam_1(A_39, '#skF_5')=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_267, c_118])).
% 2.53/1.34  tff(c_347, plain, (~r1_tarski(k1_setfam_1('#skF_6'), k8_setfam_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_34])).
% 2.53/1.34  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_385, c_273, c_347])).
% 2.53/1.34  tff(c_397, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_264])).
% 2.53/1.34  tff(c_36, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.53/1.34  tff(c_32, plain, (![B_23, A_22]: (r1_tarski(k1_setfam_1(B_23), k1_setfam_1(A_22)) | k1_xboole_0=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.53/1.34  tff(c_412, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_266])).
% 2.53/1.34  tff(c_413, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_412, c_397])).
% 2.53/1.34  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.53/1.34  tff(c_82, plain, (![C_45, B_46, A_47]: (r2_hidden(C_45, B_46) | ~r2_hidden(C_45, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.34  tff(c_211, plain, (![A_61, B_62]: (r2_hidden('#skF_3'(A_61), B_62) | ~r1_tarski(A_61, B_62) | k1_xboole_0=A_61)), inference(resolution, [status(thm)], [c_14, c_82])).
% 2.53/1.34  tff(c_81, plain, (![C_44]: (~r2_hidden(C_44, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_78])).
% 2.53/1.34  tff(c_218, plain, (![A_61]: (~r1_tarski(A_61, k1_xboole_0) | k1_xboole_0=A_61)), inference(resolution, [status(thm)], [c_211, c_81])).
% 2.53/1.34  tff(c_490, plain, (![A_82]: (~r1_tarski(A_82, '#skF_6') | A_82='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_412, c_412, c_218])).
% 2.53/1.34  tff(c_501, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_36, c_490])).
% 2.53/1.34  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_413, c_501])).
% 2.53/1.34  tff(c_510, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(splitRight, [status(thm)], [c_266])).
% 2.53/1.34  tff(c_396, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_264])).
% 2.53/1.34  tff(c_398, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k1_setfam_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_34])).
% 2.53/1.34  tff(c_512, plain, (~r1_tarski(k1_setfam_1('#skF_6'), k1_setfam_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_398])).
% 2.53/1.34  tff(c_524, plain, (k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_32, c_512])).
% 2.53/1.34  tff(c_527, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_524])).
% 2.53/1.34  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_397, c_527])).
% 2.53/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  Inference rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Ref     : 0
% 2.53/1.34  #Sup     : 92
% 2.53/1.34  #Fact    : 0
% 2.53/1.34  #Define  : 0
% 2.53/1.34  #Split   : 3
% 2.53/1.34  #Chain   : 0
% 2.53/1.34  #Close   : 0
% 2.53/1.34  
% 2.53/1.34  Ordering : KBO
% 2.53/1.34  
% 2.53/1.34  Simplification rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Subsume      : 6
% 2.53/1.34  #Demod        : 67
% 2.53/1.34  #Tautology    : 56
% 2.53/1.34  #SimpNegUnit  : 2
% 2.53/1.34  #BackRed      : 37
% 2.53/1.34  
% 2.53/1.34  #Partial instantiations: 0
% 2.53/1.34  #Strategies tried      : 1
% 2.53/1.34  
% 2.53/1.34  Timing (in seconds)
% 2.53/1.34  ----------------------
% 2.53/1.34  Preprocessing        : 0.32
% 2.53/1.34  Parsing              : 0.17
% 2.53/1.34  CNF conversion       : 0.02
% 2.53/1.34  Main loop            : 0.27
% 2.53/1.34  Inferencing          : 0.10
% 2.53/1.34  Reduction            : 0.08
% 2.53/1.34  Demodulation         : 0.06
% 2.53/1.34  BG Simplification    : 0.02
% 2.53/1.34  Subsumption          : 0.05
% 2.53/1.34  Abstraction          : 0.02
% 2.53/1.34  MUC search           : 0.00
% 2.53/1.34  Cooper               : 0.00
% 2.53/1.34  Total                : 0.63
% 2.53/1.34  Index Insertion      : 0.00
% 2.53/1.34  Index Deletion       : 0.00
% 2.53/1.34  Index Matching       : 0.00
% 2.53/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
