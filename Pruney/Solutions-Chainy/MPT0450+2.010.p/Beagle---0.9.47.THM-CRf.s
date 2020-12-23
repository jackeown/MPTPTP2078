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
% DateTime   : Thu Dec  3 09:58:37 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 251 expanded)
%              Number of leaves         :   35 ( 100 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 429 expanded)
%              Number of equality atoms :    9 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_66,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_26,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_167,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_1'(A_76,B_77),A_76)
      | r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_205,plain,(
    ! [A_82,B_83,B_84] :
      ( ~ r1_xboole_0(A_82,B_83)
      | r1_tarski(k3_xboole_0(A_82,B_83),B_84) ) ),
    inference(resolution,[status(thm)],[c_167,c_10])).

tff(c_34,plain,(
    ! [A_33] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_67,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_71,plain,(
    ! [A_33] : r1_tarski(k1_xboole_0,A_33) ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_96,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_103,plain,(
    ! [A_33] :
      ( k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_71,c_96])).

tff(c_231,plain,(
    ! [A_88,B_89] :
      ( k3_xboole_0(A_88,B_89) = k1_xboole_0
      | ~ r1_xboole_0(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_205,c_103])).

tff(c_236,plain,(
    ! [A_90] : k3_xboole_0(A_90,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_231])).

tff(c_22,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_253,plain,(
    ! [A_90] : k2_xboole_0(A_90,k1_xboole_0) = A_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_22])).

tff(c_235,plain,(
    ! [A_23] : k3_xboole_0(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_231])).

tff(c_364,plain,(
    ! [A_108,B_109,C_110] : r1_tarski(k2_xboole_0(k3_xboole_0(A_108,B_109),k3_xboole_0(A_108,C_110)),k2_xboole_0(B_109,C_110)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_378,plain,(
    ! [A_23,B_109] : r1_tarski(k2_xboole_0(k3_xboole_0(A_23,B_109),k1_xboole_0),k2_xboole_0(B_109,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_364])).

tff(c_394,plain,(
    ! [A_111,B_112] : r1_tarski(k3_xboole_0(A_111,B_112),B_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_378])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_146,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_153,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(A_36)
      | ~ v1_relat_1(B_37)
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_40,c_146])).

tff(c_410,plain,(
    ! [A_111,B_112] :
      ( v1_relat_1(k3_xboole_0(A_111,B_112))
      | ~ v1_relat_1(B_112) ) ),
    inference(resolution,[status(thm)],[c_394,c_153])).

tff(c_391,plain,(
    ! [A_23,B_109] : r1_tarski(k3_xboole_0(A_23,B_109),B_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_378])).

tff(c_46,plain,(
    ! [A_44,B_46] :
      ( r1_tarski(k3_relat_1(A_44),k3_relat_1(B_46))
      | ~ r1_tarski(A_44,B_46)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(k3_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_488,plain,(
    ! [A_123,B_124,C_125] :
      ( r1_tarski(A_123,k3_xboole_0(B_124,C_125))
      | ~ r1_tarski(A_123,C_125)
      | ~ r1_tarski(A_123,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_519,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_488,c_48])).

tff(c_748,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_519])).

tff(c_834,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_748])).

tff(c_837,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18,c_834])).

tff(c_840,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_410,c_837])).

tff(c_850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_840])).

tff(c_851,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_938,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_851])).

tff(c_941,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_391,c_938])).

tff(c_955,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_410,c_941])).

tff(c_965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_955])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:08:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.38  
% 2.84/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.84/1.38  
% 2.84/1.38  %Foreground sorts:
% 2.84/1.38  
% 2.84/1.38  
% 2.84/1.38  %Background operators:
% 2.84/1.38  
% 2.84/1.38  
% 2.84/1.38  %Foreground operators:
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.38  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.84/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.84/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.84/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.84/1.38  
% 2.84/1.40  tff(f_110, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 2.84/1.40  tff(f_66, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.84/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.84/1.40  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.84/1.40  tff(f_74, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.84/1.40  tff(f_80, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.84/1.40  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.84/1.40  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.84/1.40  tff(f_64, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.84/1.40  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.84/1.40  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.84/1.40  tff(f_54, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.84/1.40  tff(f_60, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.84/1.40  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.84/1.40  tff(c_26, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.40  tff(c_167, plain, (![A_76, B_77]: (r2_hidden('#skF_1'(A_76, B_77), A_76) | r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.84/1.40  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.84/1.40  tff(c_205, plain, (![A_82, B_83, B_84]: (~r1_xboole_0(A_82, B_83) | r1_tarski(k3_xboole_0(A_82, B_83), B_84))), inference(resolution, [status(thm)], [c_167, c_10])).
% 2.84/1.40  tff(c_34, plain, (![A_33]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.40  tff(c_67, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.84/1.40  tff(c_71, plain, (![A_33]: (r1_tarski(k1_xboole_0, A_33))), inference(resolution, [status(thm)], [c_34, c_67])).
% 2.84/1.40  tff(c_96, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.84/1.40  tff(c_103, plain, (![A_33]: (k1_xboole_0=A_33 | ~r1_tarski(A_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_71, c_96])).
% 2.84/1.40  tff(c_231, plain, (![A_88, B_89]: (k3_xboole_0(A_88, B_89)=k1_xboole_0 | ~r1_xboole_0(A_88, B_89))), inference(resolution, [status(thm)], [c_205, c_103])).
% 2.84/1.40  tff(c_236, plain, (![A_90]: (k3_xboole_0(A_90, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_231])).
% 2.84/1.40  tff(c_22, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k3_xboole_0(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.84/1.40  tff(c_253, plain, (![A_90]: (k2_xboole_0(A_90, k1_xboole_0)=A_90)), inference(superposition, [status(thm), theory('equality')], [c_236, c_22])).
% 2.84/1.40  tff(c_235, plain, (![A_23]: (k3_xboole_0(A_23, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_231])).
% 2.84/1.40  tff(c_364, plain, (![A_108, B_109, C_110]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_108, B_109), k3_xboole_0(A_108, C_110)), k2_xboole_0(B_109, C_110)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.84/1.40  tff(c_378, plain, (![A_23, B_109]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_23, B_109), k1_xboole_0), k2_xboole_0(B_109, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_364])).
% 2.84/1.40  tff(c_394, plain, (![A_111, B_112]: (r1_tarski(k3_xboole_0(A_111, B_112), B_112))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_378])).
% 2.84/1.40  tff(c_40, plain, (![A_36, B_37]: (m1_subset_1(A_36, k1_zfmisc_1(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.84/1.40  tff(c_146, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.84/1.40  tff(c_153, plain, (![A_36, B_37]: (v1_relat_1(A_36) | ~v1_relat_1(B_37) | ~r1_tarski(A_36, B_37))), inference(resolution, [status(thm)], [c_40, c_146])).
% 2.84/1.40  tff(c_410, plain, (![A_111, B_112]: (v1_relat_1(k3_xboole_0(A_111, B_112)) | ~v1_relat_1(B_112))), inference(resolution, [status(thm)], [c_394, c_153])).
% 2.84/1.40  tff(c_391, plain, (![A_23, B_109]: (r1_tarski(k3_xboole_0(A_23, B_109), B_109))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_378])).
% 2.84/1.40  tff(c_46, plain, (![A_44, B_46]: (r1_tarski(k3_relat_1(A_44), k3_relat_1(B_46)) | ~r1_tarski(A_44, B_46) | ~v1_relat_1(B_46) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.84/1.40  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.84/1.40  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(k3_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.40  tff(c_488, plain, (![A_123, B_124, C_125]: (r1_tarski(A_123, k3_xboole_0(B_124, C_125)) | ~r1_tarski(A_123, C_125) | ~r1_tarski(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.84/1.40  tff(c_48, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.84/1.40  tff(c_519, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_488, c_48])).
% 2.84/1.40  tff(c_748, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_519])).
% 2.84/1.40  tff(c_834, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_748])).
% 2.84/1.40  tff(c_837, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18, c_834])).
% 2.84/1.40  tff(c_840, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_410, c_837])).
% 2.84/1.40  tff(c_850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_840])).
% 2.84/1.40  tff(c_851, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_519])).
% 2.84/1.40  tff(c_938, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_851])).
% 2.84/1.40  tff(c_941, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_391, c_938])).
% 2.84/1.40  tff(c_955, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_410, c_941])).
% 2.84/1.40  tff(c_965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_955])).
% 2.84/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.40  
% 2.84/1.40  Inference rules
% 2.84/1.40  ----------------------
% 2.84/1.40  #Ref     : 0
% 2.84/1.40  #Sup     : 208
% 2.84/1.40  #Fact    : 0
% 2.84/1.40  #Define  : 0
% 2.84/1.40  #Split   : 4
% 2.84/1.40  #Chain   : 0
% 2.84/1.40  #Close   : 0
% 2.84/1.40  
% 2.84/1.40  Ordering : KBO
% 2.84/1.40  
% 2.84/1.40  Simplification rules
% 2.84/1.40  ----------------------
% 2.84/1.40  #Subsume      : 12
% 2.84/1.40  #Demod        : 110
% 2.84/1.40  #Tautology    : 118
% 2.84/1.40  #SimpNegUnit  : 11
% 2.84/1.40  #BackRed      : 5
% 2.84/1.40  
% 2.84/1.40  #Partial instantiations: 0
% 2.84/1.40  #Strategies tried      : 1
% 2.84/1.40  
% 2.84/1.40  Timing (in seconds)
% 2.84/1.40  ----------------------
% 2.84/1.40  Preprocessing        : 0.31
% 2.84/1.40  Parsing              : 0.17
% 2.84/1.40  CNF conversion       : 0.02
% 2.84/1.40  Main loop            : 0.32
% 2.84/1.40  Inferencing          : 0.12
% 2.84/1.40  Reduction            : 0.10
% 2.84/1.40  Demodulation         : 0.07
% 2.84/1.40  BG Simplification    : 0.02
% 2.84/1.40  Subsumption          : 0.05
% 2.84/1.40  Abstraction          : 0.02
% 2.84/1.40  MUC search           : 0.00
% 2.84/1.40  Cooper               : 0.00
% 2.84/1.40  Total                : 0.66
% 2.84/1.40  Index Insertion      : 0.00
% 2.84/1.40  Index Deletion       : 0.00
% 2.84/1.40  Index Matching       : 0.00
% 2.84/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
