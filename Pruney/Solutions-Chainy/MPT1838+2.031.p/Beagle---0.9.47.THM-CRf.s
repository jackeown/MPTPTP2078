%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:18 EST 2020

% Result     : Theorem 5.70s
% Output     : CNFRefutation 5.77s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 219 expanded)
%              Number of leaves         :   35 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  139 ( 477 expanded)
%              Number of equality atoms :   52 ( 135 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_99,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_66,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_70,plain,(
    v1_zfmisc_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_62,plain,(
    ! [A_35] :
      ( k6_domain_1(A_35,'#skF_5'(A_35)) = A_35
      | ~ v1_zfmisc_1(A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_64,plain,(
    ! [A_35] :
      ( m1_subset_1('#skF_5'(A_35),A_35)
      | ~ v1_zfmisc_1(A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_895,plain,(
    ! [A_3132,B_3133] :
      ( k6_domain_1(A_3132,B_3133) = k1_tarski(B_3133)
      | ~ m1_subset_1(B_3133,A_3132)
      | v1_xboole_0(A_3132) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2342,plain,(
    ! [A_4979] :
      ( k6_domain_1(A_4979,'#skF_5'(A_4979)) = k1_tarski('#skF_5'(A_4979))
      | ~ v1_zfmisc_1(A_4979)
      | v1_xboole_0(A_4979) ) ),
    inference(resolution,[status(thm)],[c_64,c_895])).

tff(c_5169,plain,(
    ! [A_10442] :
      ( k1_tarski('#skF_5'(A_10442)) = A_10442
      | ~ v1_zfmisc_1(A_10442)
      | v1_xboole_0(A_10442)
      | ~ v1_zfmisc_1(A_10442)
      | v1_xboole_0(A_10442) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2342])).

tff(c_24,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_91,plain,(
    ! [B_45,A_46] :
      ( ~ r2_hidden(B_45,A_46)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [C_20] : ~ v1_xboole_0(k1_tarski(C_20)) ),
    inference(resolution,[status(thm)],[c_24,c_91])).

tff(c_104,plain,(
    ! [A_51] :
      ( v1_xboole_0(A_51)
      | r2_hidden('#skF_1'(A_51),A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_108,plain,(
    ! [A_16] :
      ( '#skF_1'(k1_tarski(A_16)) = A_16
      | v1_xboole_0(k1_tarski(A_16)) ) ),
    inference(resolution,[status(thm)],[c_104,c_22])).

tff(c_114,plain,(
    ! [A_16] : '#skF_1'(k1_tarski(A_16)) = A_16 ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_108])).

tff(c_5765,plain,(
    ! [A_11007] :
      ( '#skF_5'(A_11007) = '#skF_1'(A_11007)
      | ~ v1_zfmisc_1(A_11007)
      | v1_xboole_0(A_11007)
      | ~ v1_zfmisc_1(A_11007)
      | v1_xboole_0(A_11007) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5169,c_114])).

tff(c_5774,plain,
    ( '#skF_5'('#skF_7') = '#skF_1'('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_5765])).

tff(c_5777,plain,
    ( '#skF_5'('#skF_7') = '#skF_1'('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5774])).

tff(c_5778,plain,(
    '#skF_5'('#skF_7') = '#skF_1'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5777])).

tff(c_2372,plain,(
    ! [A_35] :
      ( k1_tarski('#skF_5'(A_35)) = A_35
      | ~ v1_zfmisc_1(A_35)
      | v1_xboole_0(A_35)
      | ~ v1_zfmisc_1(A_35)
      | v1_xboole_0(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2342])).

tff(c_5782,plain,
    ( k1_tarski('#skF_1'('#skF_7')) = '#skF_7'
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5778,c_2372])).

tff(c_5803,plain,
    ( k1_tarski('#skF_1'('#skF_7')) = '#skF_7'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_5782])).

tff(c_5804,plain,(
    k1_tarski('#skF_1'('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5803])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_140,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_152,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_140])).

tff(c_216,plain,(
    ! [A_73,B_74] : k2_xboole_0(A_73,k4_xboole_0(B_74,A_73)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_232,plain,(
    k2_xboole_0('#skF_7',k1_xboole_0) = k2_xboole_0('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_216])).

tff(c_239,plain,(
    k2_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_232])).

tff(c_829,plain,(
    ! [A_3125,C_3126,B_3127] :
      ( k1_tarski(A_3125) = C_3126
      | k1_xboole_0 = C_3126
      | k2_xboole_0(B_3127,C_3126) != k1_tarski(A_3125) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_835,plain,(
    ! [A_3125] :
      ( k1_tarski(A_3125) = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k1_tarski(A_3125) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_829])).

tff(c_872,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_835])).

tff(c_18,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_277,plain,(
    ! [C_77,B_78,A_79] :
      ( r2_hidden(C_77,B_78)
      | ~ r2_hidden(C_77,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_320,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_1'(A_87),B_88)
      | ~ r1_tarski(A_87,B_88)
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_4,c_277])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_337,plain,(
    ! [B_89,A_90] :
      ( ~ v1_xboole_0(B_89)
      | ~ r1_tarski(A_90,B_89)
      | v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_320,c_2])).

tff(c_356,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(A_13)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_337])).

tff(c_359,plain,(
    ! [A_13] : ~ v1_xboole_0(A_13) ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_285,plain,(
    ! [A_1,B_78] :
      ( r2_hidden('#skF_1'(A_1),B_78)
      | ~ r1_tarski(A_1,B_78)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_277])).

tff(c_405,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_1'(A_98),B_99)
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_285])).

tff(c_423,plain,(
    ! [A_102,A_103] :
      ( A_102 = '#skF_1'(A_103)
      | ~ r1_tarski(A_103,k1_tarski(A_102)) ) ),
    inference(resolution,[status(thm)],[c_405,c_22])).

tff(c_619,plain,(
    '#skF_1'(k1_xboole_0) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_18,c_423])).

tff(c_440,plain,(
    ! [A_104] : A_104 = '#skF_1'(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_423])).

tff(c_774,plain,(
    ! [A_2399] : A_2399 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_440])).

tff(c_827,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_66])).

tff(c_828,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_878,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_828])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_878])).

tff(c_893,plain,(
    ! [A_3125] :
      ( k1_tarski(A_3125) = '#skF_6'
      | k1_tarski(A_3125) != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_6065,plain,(
    k1_tarski('#skF_1'('#skF_7')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_5804,c_893])).

tff(c_6093,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6065,c_5804])).

tff(c_6095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6093])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.70/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.13  
% 5.70/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.13  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4
% 5.70/2.13  
% 5.70/2.13  %Foreground sorts:
% 5.70/2.13  
% 5.70/2.13  
% 5.70/2.13  %Background operators:
% 5.70/2.13  
% 5.70/2.13  
% 5.70/2.13  %Foreground operators:
% 5.70/2.13  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.70/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.70/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.70/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.70/2.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.70/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.70/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.70/2.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.70/2.13  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.70/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.70/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.70/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.70/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.70/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.70/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.70/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.70/2.14  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.70/2.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.70/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.70/2.14  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.70/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.70/2.14  
% 5.77/2.15  tff(f_113, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.77/2.15  tff(f_99, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 5.77/2.15  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.77/2.15  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.77/2.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.77/2.15  tff(f_44, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.77/2.15  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.77/2.15  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.77/2.15  tff(f_79, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 5.77/2.15  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.77/2.15  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.77/2.15  tff(c_66, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.77/2.15  tff(c_72, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.77/2.15  tff(c_70, plain, (v1_zfmisc_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.77/2.15  tff(c_62, plain, (![A_35]: (k6_domain_1(A_35, '#skF_5'(A_35))=A_35 | ~v1_zfmisc_1(A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.77/2.15  tff(c_64, plain, (![A_35]: (m1_subset_1('#skF_5'(A_35), A_35) | ~v1_zfmisc_1(A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.77/2.15  tff(c_895, plain, (![A_3132, B_3133]: (k6_domain_1(A_3132, B_3133)=k1_tarski(B_3133) | ~m1_subset_1(B_3133, A_3132) | v1_xboole_0(A_3132))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.77/2.15  tff(c_2342, plain, (![A_4979]: (k6_domain_1(A_4979, '#skF_5'(A_4979))=k1_tarski('#skF_5'(A_4979)) | ~v1_zfmisc_1(A_4979) | v1_xboole_0(A_4979))), inference(resolution, [status(thm)], [c_64, c_895])).
% 5.77/2.15  tff(c_5169, plain, (![A_10442]: (k1_tarski('#skF_5'(A_10442))=A_10442 | ~v1_zfmisc_1(A_10442) | v1_xboole_0(A_10442) | ~v1_zfmisc_1(A_10442) | v1_xboole_0(A_10442))), inference(superposition, [status(thm), theory('equality')], [c_62, c_2342])).
% 5.77/2.15  tff(c_24, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.77/2.15  tff(c_91, plain, (![B_45, A_46]: (~r2_hidden(B_45, A_46) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.77/2.15  tff(c_95, plain, (![C_20]: (~v1_xboole_0(k1_tarski(C_20)))), inference(resolution, [status(thm)], [c_24, c_91])).
% 5.77/2.15  tff(c_104, plain, (![A_51]: (v1_xboole_0(A_51) | r2_hidden('#skF_1'(A_51), A_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.77/2.15  tff(c_22, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.77/2.15  tff(c_108, plain, (![A_16]: ('#skF_1'(k1_tarski(A_16))=A_16 | v1_xboole_0(k1_tarski(A_16)))), inference(resolution, [status(thm)], [c_104, c_22])).
% 5.77/2.15  tff(c_114, plain, (![A_16]: ('#skF_1'(k1_tarski(A_16))=A_16)), inference(negUnitSimplification, [status(thm)], [c_95, c_108])).
% 5.77/2.15  tff(c_5765, plain, (![A_11007]: ('#skF_5'(A_11007)='#skF_1'(A_11007) | ~v1_zfmisc_1(A_11007) | v1_xboole_0(A_11007) | ~v1_zfmisc_1(A_11007) | v1_xboole_0(A_11007))), inference(superposition, [status(thm), theory('equality')], [c_5169, c_114])).
% 5.77/2.15  tff(c_5774, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_70, c_5765])).
% 5.77/2.15  tff(c_5777, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5774])).
% 5.77/2.15  tff(c_5778, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_72, c_5777])).
% 5.77/2.15  tff(c_2372, plain, (![A_35]: (k1_tarski('#skF_5'(A_35))=A_35 | ~v1_zfmisc_1(A_35) | v1_xboole_0(A_35) | ~v1_zfmisc_1(A_35) | v1_xboole_0(A_35))), inference(superposition, [status(thm), theory('equality')], [c_62, c_2342])).
% 5.77/2.15  tff(c_5782, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7' | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5778, c_2372])).
% 5.77/2.15  tff(c_5803, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_5782])).
% 5.77/2.15  tff(c_5804, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_72, c_5803])).
% 5.77/2.15  tff(c_74, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.77/2.15  tff(c_16, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.77/2.15  tff(c_68, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.77/2.15  tff(c_140, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.77/2.15  tff(c_152, plain, (k4_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_140])).
% 5.77/2.15  tff(c_216, plain, (![A_73, B_74]: (k2_xboole_0(A_73, k4_xboole_0(B_74, A_73))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.77/2.15  tff(c_232, plain, (k2_xboole_0('#skF_7', k1_xboole_0)=k2_xboole_0('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_152, c_216])).
% 5.77/2.15  tff(c_239, plain, (k2_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_232])).
% 5.77/2.15  tff(c_829, plain, (![A_3125, C_3126, B_3127]: (k1_tarski(A_3125)=C_3126 | k1_xboole_0=C_3126 | k2_xboole_0(B_3127, C_3126)!=k1_tarski(A_3125))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.77/2.15  tff(c_835, plain, (![A_3125]: (k1_tarski(A_3125)='#skF_6' | k1_xboole_0='#skF_6' | k1_tarski(A_3125)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_239, c_829])).
% 5.77/2.15  tff(c_872, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_835])).
% 5.77/2.15  tff(c_18, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.77/2.15  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.77/2.15  tff(c_277, plain, (![C_77, B_78, A_79]: (r2_hidden(C_77, B_78) | ~r2_hidden(C_77, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.77/2.15  tff(c_320, plain, (![A_87, B_88]: (r2_hidden('#skF_1'(A_87), B_88) | ~r1_tarski(A_87, B_88) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_4, c_277])).
% 5.77/2.15  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.77/2.15  tff(c_337, plain, (![B_89, A_90]: (~v1_xboole_0(B_89) | ~r1_tarski(A_90, B_89) | v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_320, c_2])).
% 5.77/2.15  tff(c_356, plain, (![A_13]: (~v1_xboole_0(A_13) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_337])).
% 5.77/2.15  tff(c_359, plain, (![A_13]: (~v1_xboole_0(A_13))), inference(splitLeft, [status(thm)], [c_356])).
% 5.77/2.15  tff(c_285, plain, (![A_1, B_78]: (r2_hidden('#skF_1'(A_1), B_78) | ~r1_tarski(A_1, B_78) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_277])).
% 5.77/2.15  tff(c_405, plain, (![A_98, B_99]: (r2_hidden('#skF_1'(A_98), B_99) | ~r1_tarski(A_98, B_99))), inference(negUnitSimplification, [status(thm)], [c_359, c_285])).
% 5.77/2.15  tff(c_423, plain, (![A_102, A_103]: (A_102='#skF_1'(A_103) | ~r1_tarski(A_103, k1_tarski(A_102)))), inference(resolution, [status(thm)], [c_405, c_22])).
% 5.77/2.15  tff(c_619, plain, ('#skF_1'(k1_xboole_0)='#skF_6'), inference(resolution, [status(thm)], [c_18, c_423])).
% 5.77/2.15  tff(c_440, plain, (![A_104]: (A_104='#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_423])).
% 5.77/2.15  tff(c_774, plain, (![A_2399]: (A_2399='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_619, c_440])).
% 5.77/2.15  tff(c_827, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_774, c_66])).
% 5.77/2.15  tff(c_828, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_356])).
% 5.77/2.15  tff(c_878, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_872, c_828])).
% 5.77/2.15  tff(c_892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_878])).
% 5.77/2.15  tff(c_893, plain, (![A_3125]: (k1_tarski(A_3125)='#skF_6' | k1_tarski(A_3125)!='#skF_7')), inference(splitRight, [status(thm)], [c_835])).
% 5.77/2.15  tff(c_6065, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_5804, c_893])).
% 5.77/2.15  tff(c_6093, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6065, c_5804])).
% 5.77/2.15  tff(c_6095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_6093])).
% 5.77/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.15  
% 5.77/2.15  Inference rules
% 5.77/2.15  ----------------------
% 5.77/2.15  #Ref     : 2
% 5.77/2.15  #Sup     : 1078
% 5.77/2.15  #Fact    : 2
% 5.77/2.15  #Define  : 0
% 5.77/2.15  #Split   : 10
% 5.77/2.15  #Chain   : 0
% 5.77/2.15  #Close   : 0
% 5.77/2.15  
% 5.77/2.15  Ordering : KBO
% 5.77/2.15  
% 5.77/2.15  Simplification rules
% 5.77/2.15  ----------------------
% 5.77/2.15  #Subsume      : 317
% 5.77/2.15  #Demod        : 205
% 5.77/2.15  #Tautology    : 273
% 5.77/2.15  #SimpNegUnit  : 88
% 5.77/2.15  #BackRed      : 35
% 5.77/2.15  
% 5.77/2.15  #Partial instantiations: 4008
% 5.77/2.15  #Strategies tried      : 1
% 5.77/2.15  
% 5.77/2.15  Timing (in seconds)
% 5.77/2.15  ----------------------
% 5.77/2.15  Preprocessing        : 0.33
% 5.77/2.15  Parsing              : 0.17
% 5.77/2.15  CNF conversion       : 0.03
% 5.77/2.15  Main loop            : 1.06
% 5.77/2.15  Inferencing          : 0.48
% 5.77/2.15  Reduction            : 0.27
% 5.77/2.15  Demodulation         : 0.17
% 5.77/2.15  BG Simplification    : 0.04
% 5.77/2.15  Subsumption          : 0.20
% 5.77/2.15  Abstraction          : 0.04
% 5.77/2.16  MUC search           : 0.00
% 5.77/2.16  Cooper               : 0.00
% 5.77/2.16  Total                : 1.43
% 5.77/2.16  Index Insertion      : 0.00
% 5.77/2.16  Index Deletion       : 0.00
% 5.77/2.16  Index Matching       : 0.00
% 5.77/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
