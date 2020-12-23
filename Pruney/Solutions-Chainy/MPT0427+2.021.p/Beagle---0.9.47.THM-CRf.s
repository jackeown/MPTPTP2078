%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:59 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 174 expanded)
%              Number of leaves         :   28 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 337 expanded)
%              Number of equality atoms :   38 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_203,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k8_setfam_1(A_55,B_56),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [C_8,A_4] :
      ( r1_tarski(C_8,A_4)
      | ~ r2_hidden(C_8,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_100,plain,(
    ! [A_37,A_4] :
      ( r1_tarski(A_37,A_4)
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ m1_subset_1(A_37,k1_zfmisc_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_96,c_10])).

tff(c_103,plain,(
    ! [A_37,A_4] :
      ( r1_tarski(A_37,A_4)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(A_4)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_100])).

tff(c_319,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k8_setfam_1(A_76,B_77),A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(resolution,[status(thm)],[c_203,c_103])).

tff(c_339,plain,(
    r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_319])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_126,plain,(
    ! [A_41,B_42] :
      ( k6_setfam_1(A_41,B_42) = k1_setfam_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_138,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_126])).

tff(c_588,plain,(
    ! [A_101,B_102] :
      ( k8_setfam_1(A_101,B_102) = k6_setfam_1(A_101,B_102)
      | k1_xboole_0 = B_102
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k1_zfmisc_1(A_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_606,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_588])).

tff(c_618,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_606])).

tff(c_647,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_618])).

tff(c_24,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_11] :
      ( k8_setfam_1(A_11,k1_xboole_0) = A_11
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    ! [A_11] : k8_setfam_1(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_659,plain,(
    ! [A_11] : k8_setfam_1(A_11,'#skF_4') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_48])).

tff(c_340,plain,(
    r1_tarski(k8_setfam_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_319])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_348,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k8_setfam_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_340,c_2])).

tff(c_457,plain,(
    ~ r1_tarski('#skF_3',k8_setfam_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_688,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_457])).

tff(c_693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_688])).

tff(c_695,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_42,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_setfam_1(B_23),k1_setfam_1(A_22))
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_137,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_126])).

tff(c_603,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_588])).

tff(c_616,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_603])).

tff(c_622,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_616])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_635,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_8])).

tff(c_69,plain,(
    ! [B_34,A_35] :
      ( B_34 = A_35
      | ~ r1_tarski(B_34,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_95,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_95])).

tff(c_645,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_616])).

tff(c_694,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_40,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_763,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_40])).

tff(c_786,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_763])).

tff(c_805,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_786])).

tff(c_808,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_805])).

tff(c_810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_695,c_808])).

tff(c_811,plain,(
    k8_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_814,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_40])).

tff(c_818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_814])).

tff(c_819,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_821,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_40])).

tff(c_826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.48  
% 3.19/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.48  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.19/1.48  
% 3.19/1.48  %Foreground sorts:
% 3.19/1.48  
% 3.19/1.48  
% 3.19/1.48  %Background operators:
% 3.19/1.48  
% 3.19/1.48  
% 3.19/1.48  %Foreground operators:
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.48  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.19/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.48  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.19/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.19/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.19/1.48  
% 3.19/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.19/1.49  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.19/1.49  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.19/1.49  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.19/1.49  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.19/1.49  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.19/1.49  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.19/1.49  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.19/1.49  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.19/1.49  tff(f_82, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.19/1.49  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.19/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.49  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.49  tff(c_203, plain, (![A_55, B_56]: (m1_subset_1(k8_setfam_1(A_55, B_56), k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.49  tff(c_22, plain, (![A_9]: (~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.19/1.49  tff(c_96, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | v1_xboole_0(B_38) | ~m1_subset_1(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.19/1.49  tff(c_10, plain, (![C_8, A_4]: (r1_tarski(C_8, A_4) | ~r2_hidden(C_8, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.19/1.49  tff(c_100, plain, (![A_37, A_4]: (r1_tarski(A_37, A_4) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~m1_subset_1(A_37, k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_96, c_10])).
% 3.19/1.49  tff(c_103, plain, (![A_37, A_4]: (r1_tarski(A_37, A_4) | ~m1_subset_1(A_37, k1_zfmisc_1(A_4)))), inference(negUnitSimplification, [status(thm)], [c_22, c_100])).
% 3.19/1.49  tff(c_319, plain, (![A_76, B_77]: (r1_tarski(k8_setfam_1(A_76, B_77), A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(resolution, [status(thm)], [c_203, c_103])).
% 3.19/1.49  tff(c_339, plain, (r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_44, c_319])).
% 3.19/1.49  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.49  tff(c_126, plain, (![A_41, B_42]: (k6_setfam_1(A_41, B_42)=k1_setfam_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_41))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.19/1.49  tff(c_138, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_126])).
% 3.19/1.49  tff(c_588, plain, (![A_101, B_102]: (k8_setfam_1(A_101, B_102)=k6_setfam_1(A_101, B_102) | k1_xboole_0=B_102 | ~m1_subset_1(B_102, k1_zfmisc_1(k1_zfmisc_1(A_101))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.19/1.49  tff(c_606, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_588])).
% 3.19/1.49  tff(c_618, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_606])).
% 3.19/1.49  tff(c_647, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_618])).
% 3.19/1.49  tff(c_24, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.19/1.49  tff(c_26, plain, (![A_11]: (k8_setfam_1(A_11, k1_xboole_0)=A_11 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.19/1.49  tff(c_48, plain, (![A_11]: (k8_setfam_1(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 3.19/1.49  tff(c_659, plain, (![A_11]: (k8_setfam_1(A_11, '#skF_4')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_647, c_48])).
% 3.19/1.49  tff(c_340, plain, (r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_46, c_319])).
% 3.19/1.49  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.49  tff(c_348, plain, (k8_setfam_1('#skF_3', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k8_setfam_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_340, c_2])).
% 3.19/1.49  tff(c_457, plain, (~r1_tarski('#skF_3', k8_setfam_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_348])).
% 3.19/1.49  tff(c_688, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_659, c_457])).
% 3.19/1.49  tff(c_693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_688])).
% 3.19/1.49  tff(c_695, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_618])).
% 3.19/1.49  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.49  tff(c_38, plain, (![B_23, A_22]: (r1_tarski(k1_setfam_1(B_23), k1_setfam_1(A_22)) | k1_xboole_0=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.19/1.49  tff(c_137, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_126])).
% 3.19/1.49  tff(c_603, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_588])).
% 3.19/1.49  tff(c_616, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_603])).
% 3.19/1.49  tff(c_622, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_616])).
% 3.19/1.49  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.49  tff(c_635, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_8])).
% 3.19/1.49  tff(c_69, plain, (![B_34, A_35]: (B_34=A_35 | ~r1_tarski(B_34, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.49  tff(c_81, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_69])).
% 3.19/1.49  tff(c_95, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_81])).
% 3.19/1.49  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_635, c_95])).
% 3.19/1.49  tff(c_645, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_616])).
% 3.19/1.49  tff(c_694, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_618])).
% 3.19/1.49  tff(c_40, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.49  tff(c_763, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_694, c_40])).
% 3.19/1.49  tff(c_786, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_645, c_763])).
% 3.19/1.49  tff(c_805, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_786])).
% 3.19/1.49  tff(c_808, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_805])).
% 3.19/1.49  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_695, c_808])).
% 3.19/1.49  tff(c_811, plain, (k8_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_348])).
% 3.19/1.49  tff(c_814, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_811, c_40])).
% 3.19/1.49  tff(c_818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_339, c_814])).
% 3.19/1.49  tff(c_819, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_81])).
% 3.19/1.49  tff(c_821, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_819, c_40])).
% 3.19/1.49  tff(c_826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_821])).
% 3.19/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.49  
% 3.19/1.49  Inference rules
% 3.19/1.49  ----------------------
% 3.19/1.49  #Ref     : 0
% 3.19/1.49  #Sup     : 160
% 3.19/1.49  #Fact    : 0
% 3.19/1.49  #Define  : 0
% 3.19/1.50  #Split   : 11
% 3.19/1.50  #Chain   : 0
% 3.19/1.50  #Close   : 0
% 3.19/1.50  
% 3.19/1.50  Ordering : KBO
% 3.19/1.50  
% 3.19/1.50  Simplification rules
% 3.19/1.50  ----------------------
% 3.19/1.50  #Subsume      : 1
% 3.19/1.50  #Demod        : 129
% 3.19/1.50  #Tautology    : 68
% 3.19/1.50  #SimpNegUnit  : 2
% 3.19/1.50  #BackRed      : 44
% 3.19/1.50  
% 3.19/1.50  #Partial instantiations: 0
% 3.19/1.50  #Strategies tried      : 1
% 3.19/1.50  
% 3.19/1.50  Timing (in seconds)
% 3.19/1.50  ----------------------
% 3.19/1.50  Preprocessing        : 0.31
% 3.19/1.50  Parsing              : 0.16
% 3.19/1.50  CNF conversion       : 0.02
% 3.19/1.50  Main loop            : 0.40
% 3.19/1.50  Inferencing          : 0.14
% 3.19/1.50  Reduction            : 0.12
% 3.19/1.50  Demodulation         : 0.08
% 3.19/1.50  BG Simplification    : 0.02
% 3.19/1.50  Subsumption          : 0.09
% 3.19/1.50  Abstraction          : 0.02
% 3.19/1.50  MUC search           : 0.00
% 3.19/1.50  Cooper               : 0.00
% 3.19/1.50  Total                : 0.74
% 3.19/1.50  Index Insertion      : 0.00
% 3.19/1.50  Index Deletion       : 0.00
% 3.19/1.50  Index Matching       : 0.00
% 3.19/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
