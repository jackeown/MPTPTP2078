%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:33 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 193 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  132 ( 391 expanded)
%              Number of equality atoms :   27 (  55 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_110,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ! [A_42,B_43] : k2_xboole_0(k1_tarski(A_42),B_43) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_79,plain,(
    ! [A_42] : k1_tarski(A_42) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_75])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_50,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_258,plain,(
    ! [A_80,B_81] :
      ( k6_domain_1(A_80,B_81) = k1_tarski(B_81)
      | ~ m1_subset_1(B_81,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_270,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_258])).

tff(c_276,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_270])).

tff(c_669,plain,(
    ! [A_112,B_113] :
      ( m1_subset_1(k6_domain_1(A_112,B_113),k1_zfmisc_1(A_112))
      | ~ m1_subset_1(B_113,A_112)
      | v1_xboole_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_680,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_669])).

tff(c_685,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_680])).

tff(c_686,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_685])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_697,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_686,c_34])).

tff(c_827,plain,(
    ! [B_121,A_122] :
      ( B_121 = A_122
      | ~ r1_tarski(A_122,B_121)
      | ~ v1_zfmisc_1(B_121)
      | v1_xboole_0(B_121)
      | v1_xboole_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_830,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_697,c_827])).

tff(c_845,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_830])).

tff(c_846,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_845])).

tff(c_853,plain,(
    v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_846])).

tff(c_197,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_208,plain,(
    ! [A_67,B_68] :
      ( ~ v1_xboole_0(A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_197,c_2])).

tff(c_26,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_143,plain,(
    ! [A_59] : r1_tarski(k1_xboole_0,A_59) ),
    inference(resolution,[status(thm)],[c_26,c_123])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_146,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ r1_tarski(A_59,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_143,c_12])).

tff(c_220,plain,(
    ! [A_67] :
      ( k1_xboole_0 = A_67
      | ~ v1_xboole_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_208,c_146])).

tff(c_866,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_853,c_220])).

tff(c_874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_866])).

tff(c_875,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_846])).

tff(c_708,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_697,c_12])).

tff(c_822,plain,(
    ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_708])).

tff(c_877,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_822])).

tff(c_885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_877])).

tff(c_886,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_48,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_277,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_48])).

tff(c_1345,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_277])).

tff(c_32,plain,(
    ! [A_22] : m1_subset_1('#skF_3'(A_22),k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_134,plain,(
    ! [A_22] : r1_tarski('#skF_3'(A_22),A_22) ),
    inference(resolution,[status(thm)],[c_32,c_123])).

tff(c_1485,plain,(
    ! [B_148,A_149] :
      ( B_148 = A_149
      | ~ r1_tarski(A_149,B_148)
      | ~ v1_zfmisc_1(B_148)
      | v1_xboole_0(B_148)
      | v1_xboole_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3643,plain,(
    ! [A_234] :
      ( '#skF_3'(A_234) = A_234
      | ~ v1_zfmisc_1(A_234)
      | v1_xboole_0(A_234)
      | v1_xboole_0('#skF_3'(A_234)) ) ),
    inference(resolution,[status(thm)],[c_134,c_1485])).

tff(c_30,plain,(
    ! [A_22] : ~ v1_subset_1('#skF_3'(A_22),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1377,plain,(
    ! [B_142,A_143] :
      ( ~ v1_xboole_0(B_142)
      | v1_subset_1(B_142,A_143)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_143))
      | v1_xboole_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1389,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0('#skF_3'(A_22))
      | v1_subset_1('#skF_3'(A_22),A_22)
      | v1_xboole_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_32,c_1377])).

tff(c_1400,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0('#skF_3'(A_22))
      | v1_xboole_0(A_22) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1389])).

tff(c_3686,plain,(
    ! [A_235] :
      ( '#skF_3'(A_235) = A_235
      | ~ v1_zfmisc_1(A_235)
      | v1_xboole_0(A_235) ) ),
    inference(resolution,[status(thm)],[c_3643,c_1400])).

tff(c_3689,plain,
    ( '#skF_3'('#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_3686])).

tff(c_3692,plain,(
    '#skF_3'('#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3689])).

tff(c_3756,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3692,c_30])).

tff(c_3784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_3756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.91  
% 4.76/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.91  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 4.76/1.91  
% 4.76/1.91  %Foreground sorts:
% 4.76/1.91  
% 4.76/1.91  
% 4.76/1.91  %Background operators:
% 4.76/1.91  
% 4.76/1.91  
% 4.76/1.91  %Foreground operators:
% 4.76/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.76/1.91  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.76/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.76/1.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.76/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.76/1.91  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.76/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.76/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.76/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.76/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.76/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.76/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.76/1.91  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.76/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.76/1.91  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.76/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.76/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.76/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.76/1.91  
% 5.07/1.93  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.07/1.93  tff(f_46, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.07/1.93  tff(f_53, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.07/1.93  tff(f_122, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 5.07/1.93  tff(f_97, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.07/1.93  tff(f_90, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 5.07/1.93  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.07/1.93  tff(f_110, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.07/1.93  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.07/1.93  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.07/1.93  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.07/1.93  tff(f_73, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 5.07/1.93  tff(f_67, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_subset_1)).
% 5.07/1.93  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.07/1.93  tff(c_18, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.07/1.93  tff(c_75, plain, (![A_42, B_43]: (k2_xboole_0(k1_tarski(A_42), B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.07/1.93  tff(c_79, plain, (![A_42]: (k1_tarski(A_42)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_75])).
% 5.07/1.93  tff(c_52, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.07/1.93  tff(c_46, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.07/1.93  tff(c_50, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.07/1.93  tff(c_258, plain, (![A_80, B_81]: (k6_domain_1(A_80, B_81)=k1_tarski(B_81) | ~m1_subset_1(B_81, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.07/1.93  tff(c_270, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_258])).
% 5.07/1.93  tff(c_276, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_270])).
% 5.07/1.93  tff(c_669, plain, (![A_112, B_113]: (m1_subset_1(k6_domain_1(A_112, B_113), k1_zfmisc_1(A_112)) | ~m1_subset_1(B_113, A_112) | v1_xboole_0(A_112))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.07/1.93  tff(c_680, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_276, c_669])).
% 5.07/1.93  tff(c_685, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_680])).
% 5.07/1.93  tff(c_686, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_685])).
% 5.07/1.93  tff(c_34, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.07/1.93  tff(c_697, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_686, c_34])).
% 5.07/1.93  tff(c_827, plain, (![B_121, A_122]: (B_121=A_122 | ~r1_tarski(A_122, B_121) | ~v1_zfmisc_1(B_121) | v1_xboole_0(B_121) | v1_xboole_0(A_122))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.07/1.93  tff(c_830, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_697, c_827])).
% 5.07/1.93  tff(c_845, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_830])).
% 5.07/1.93  tff(c_846, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0(k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_845])).
% 5.07/1.93  tff(c_853, plain, (v1_xboole_0(k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_846])).
% 5.07/1.93  tff(c_197, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.07/1.93  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.07/1.93  tff(c_208, plain, (![A_67, B_68]: (~v1_xboole_0(A_67) | r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_197, c_2])).
% 5.07/1.93  tff(c_26, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.07/1.93  tff(c_123, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.07/1.93  tff(c_143, plain, (![A_59]: (r1_tarski(k1_xboole_0, A_59))), inference(resolution, [status(thm)], [c_26, c_123])).
% 5.07/1.93  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.07/1.93  tff(c_146, plain, (![A_59]: (k1_xboole_0=A_59 | ~r1_tarski(A_59, k1_xboole_0))), inference(resolution, [status(thm)], [c_143, c_12])).
% 5.07/1.93  tff(c_220, plain, (![A_67]: (k1_xboole_0=A_67 | ~v1_xboole_0(A_67))), inference(resolution, [status(thm)], [c_208, c_146])).
% 5.07/1.93  tff(c_866, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_853, c_220])).
% 5.07/1.93  tff(c_874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_866])).
% 5.07/1.93  tff(c_875, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_846])).
% 5.07/1.93  tff(c_708, plain, (k1_tarski('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_697, c_12])).
% 5.07/1.93  tff(c_822, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_708])).
% 5.07/1.93  tff(c_877, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_875, c_822])).
% 5.07/1.93  tff(c_885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_877])).
% 5.07/1.93  tff(c_886, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_708])).
% 5.07/1.93  tff(c_48, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.07/1.93  tff(c_277, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_48])).
% 5.07/1.93  tff(c_1345, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_886, c_277])).
% 5.07/1.93  tff(c_32, plain, (![A_22]: (m1_subset_1('#skF_3'(A_22), k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.07/1.93  tff(c_134, plain, (![A_22]: (r1_tarski('#skF_3'(A_22), A_22))), inference(resolution, [status(thm)], [c_32, c_123])).
% 5.07/1.93  tff(c_1485, plain, (![B_148, A_149]: (B_148=A_149 | ~r1_tarski(A_149, B_148) | ~v1_zfmisc_1(B_148) | v1_xboole_0(B_148) | v1_xboole_0(A_149))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.07/1.93  tff(c_3643, plain, (![A_234]: ('#skF_3'(A_234)=A_234 | ~v1_zfmisc_1(A_234) | v1_xboole_0(A_234) | v1_xboole_0('#skF_3'(A_234)))), inference(resolution, [status(thm)], [c_134, c_1485])).
% 5.07/1.93  tff(c_30, plain, (![A_22]: (~v1_subset_1('#skF_3'(A_22), A_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.07/1.93  tff(c_1377, plain, (![B_142, A_143]: (~v1_xboole_0(B_142) | v1_subset_1(B_142, A_143) | ~m1_subset_1(B_142, k1_zfmisc_1(A_143)) | v1_xboole_0(A_143))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.07/1.93  tff(c_1389, plain, (![A_22]: (~v1_xboole_0('#skF_3'(A_22)) | v1_subset_1('#skF_3'(A_22), A_22) | v1_xboole_0(A_22))), inference(resolution, [status(thm)], [c_32, c_1377])).
% 5.07/1.93  tff(c_1400, plain, (![A_22]: (~v1_xboole_0('#skF_3'(A_22)) | v1_xboole_0(A_22))), inference(negUnitSimplification, [status(thm)], [c_30, c_1389])).
% 5.07/1.93  tff(c_3686, plain, (![A_235]: ('#skF_3'(A_235)=A_235 | ~v1_zfmisc_1(A_235) | v1_xboole_0(A_235))), inference(resolution, [status(thm)], [c_3643, c_1400])).
% 5.07/1.93  tff(c_3689, plain, ('#skF_3'('#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_3686])).
% 5.07/1.93  tff(c_3692, plain, ('#skF_3'('#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_3689])).
% 5.07/1.93  tff(c_3756, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3692, c_30])).
% 5.07/1.93  tff(c_3784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1345, c_3756])).
% 5.07/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.07/1.93  
% 5.07/1.93  Inference rules
% 5.07/1.93  ----------------------
% 5.07/1.93  #Ref     : 0
% 5.07/1.93  #Sup     : 835
% 5.07/1.93  #Fact    : 0
% 5.07/1.93  #Define  : 0
% 5.07/1.93  #Split   : 11
% 5.07/1.93  #Chain   : 0
% 5.07/1.93  #Close   : 0
% 5.07/1.93  
% 5.07/1.93  Ordering : KBO
% 5.07/1.93  
% 5.07/1.93  Simplification rules
% 5.07/1.93  ----------------------
% 5.07/1.93  #Subsume      : 206
% 5.07/1.93  #Demod        : 417
% 5.07/1.93  #Tautology    : 282
% 5.07/1.93  #SimpNegUnit  : 117
% 5.07/1.93  #BackRed      : 46
% 5.07/1.93  
% 5.07/1.93  #Partial instantiations: 0
% 5.07/1.93  #Strategies tried      : 1
% 5.07/1.93  
% 5.07/1.93  Timing (in seconds)
% 5.07/1.93  ----------------------
% 5.07/1.93  Preprocessing        : 0.33
% 5.07/1.93  Parsing              : 0.17
% 5.07/1.93  CNF conversion       : 0.02
% 5.07/1.93  Main loop            : 0.83
% 5.07/1.93  Inferencing          : 0.28
% 5.07/1.93  Reduction            : 0.26
% 5.07/1.93  Demodulation         : 0.18
% 5.07/1.93  BG Simplification    : 0.03
% 5.07/1.93  Subsumption          : 0.18
% 5.07/1.93  Abstraction          : 0.04
% 5.07/1.93  MUC search           : 0.00
% 5.07/1.93  Cooper               : 0.00
% 5.07/1.93  Total                : 1.20
% 5.07/1.93  Index Insertion      : 0.00
% 5.07/1.93  Index Deletion       : 0.00
% 5.07/1.93  Index Matching       : 0.00
% 5.07/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
