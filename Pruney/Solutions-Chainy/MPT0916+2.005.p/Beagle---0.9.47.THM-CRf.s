%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:10 EST 2020

% Result     : Theorem 6.60s
% Output     : CNFRefutation 6.60s
% Verified   : 
% Statistics : Number of formulae       :  267 (1406 expanded)
%              Number of leaves         :   39 ( 465 expanded)
%              Depth                    :   13
%              Number of atoms          :  421 (3800 expanded)
%              Number of equality atoms :  142 ( 893 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_109,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_38,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_2'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2136,plain,(
    ! [C_267,A_268,B_269] :
      ( r2_hidden(C_267,A_268)
      | ~ r2_hidden(C_267,B_269)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(A_268)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2455,plain,(
    ! [A_319,A_320] :
      ( r2_hidden('#skF_2'(A_319),A_320)
      | ~ m1_subset_1(A_319,k1_zfmisc_1(A_320))
      | k1_xboole_0 = A_319 ) ),
    inference(resolution,[status(thm)],[c_38,c_2136])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2487,plain,(
    ! [A_322,A_323] :
      ( ~ v1_xboole_0(A_322)
      | ~ m1_subset_1(A_323,k1_zfmisc_1(A_322))
      | k1_xboole_0 = A_323 ) ),
    inference(resolution,[status(thm)],[c_2455,c_2])).

tff(c_2501,plain,
    ( ~ v1_xboole_0('#skF_5')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_46,c_2487])).

tff(c_2504,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2501])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2502,plain,
    ( ~ v1_xboole_0('#skF_4')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_48,c_2487])).

tff(c_2506,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2502])).

tff(c_42,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21] : k2_zfmisc_1(k2_zfmisc_1(A_19,B_20),C_21) = k3_zfmisc_1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2125,plain,(
    ! [A_264,C_265,B_266] :
      ( r2_hidden(k2_mcart_1(A_264),C_265)
      | ~ r2_hidden(A_264,k2_zfmisc_1(B_266,C_265)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2521,plain,(
    ! [A_328,C_329,A_330,B_331] :
      ( r2_hidden(k2_mcart_1(A_328),C_329)
      | ~ r2_hidden(A_328,k3_zfmisc_1(A_330,B_331,C_329)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2125])).

tff(c_2538,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_2521])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_82,C_83,B_84] :
      ( r2_hidden(k2_mcart_1(A_82),C_83)
      | ~ r2_hidden(A_82,k2_zfmisc_1(B_84,C_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2056,plain,(
    ! [B_259,C_260] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_259,C_260))),C_260)
      | v1_xboole_0(k2_zfmisc_1(B_259,C_260)) ) ),
    inference(resolution,[status(thm)],[c_4,c_112])).

tff(c_40,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8')
    | ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_111,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_165,plain,(
    ! [C_94,A_95,B_96] :
      ( r2_hidden(C_94,A_95)
      | ~ r2_hidden(C_94,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_613,plain,(
    ! [A_167,A_168] :
      ( r2_hidden('#skF_1'(A_167),A_168)
      | ~ m1_subset_1(A_167,k1_zfmisc_1(A_168))
      | v1_xboole_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_4,c_165])).

tff(c_643,plain,(
    ! [A_169,A_170] :
      ( ~ v1_xboole_0(A_169)
      | ~ m1_subset_1(A_170,k1_zfmisc_1(A_169))
      | v1_xboole_0(A_170) ) ),
    inference(resolution,[status(thm)],[c_613,c_2])).

tff(c_660,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_643])).

tff(c_664,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_660])).

tff(c_44,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_260,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k7_mcart_1(A_110,B_111,C_112,D_113) = k2_mcart_1(D_113)
      | ~ m1_subset_1(D_113,k3_zfmisc_1(A_110,B_111,C_112))
      | k1_xboole_0 = C_112
      | k1_xboole_0 = B_111
      | k1_xboole_0 = A_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_268,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_260])).

tff(c_275,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_285,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_6])).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_71,B_72] :
      ( r2_hidden(A_71,B_72)
      | ~ r1_tarski(k1_tarski(A_71),B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_73] : r2_hidden(A_73,k1_tarski(A_73)) ),
    inference(resolution,[status(thm)],[c_12,c_75])).

tff(c_89,plain,(
    ! [A_73] : ~ v1_xboole_0(k1_tarski(A_73)) ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k1_tarski(A_13),k1_zfmisc_1(B_14))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_140,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_xboole_0(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_147,plain,(
    ! [A_13,A_89,B_90] :
      ( v1_xboole_0(k1_tarski(A_13))
      | ~ v1_xboole_0(A_89)
      | ~ r2_hidden(A_13,k2_zfmisc_1(A_89,B_90)) ) ),
    inference(resolution,[status(thm)],[c_20,c_140])).

tff(c_151,plain,(
    ! [A_91,A_92,B_93] :
      ( ~ v1_xboole_0(A_91)
      | ~ r2_hidden(A_92,k2_zfmisc_1(A_91,B_93)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_147])).

tff(c_186,plain,(
    ! [A_99,B_100] :
      ( ~ v1_xboole_0(A_99)
      | k2_zfmisc_1(A_99,B_100) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_151])).

tff(c_193,plain,(
    ! [B_100] : k2_zfmisc_1(k1_xboole_0,B_100) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_186])).

tff(c_194,plain,(
    ! [B_101] : k2_zfmisc_1(k1_xboole_0,B_101) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_186])).

tff(c_208,plain,(
    ! [B_101,C_21] : k3_zfmisc_1(k1_xboole_0,B_101,C_21) = k2_zfmisc_1(k1_xboole_0,C_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_24])).

tff(c_222,plain,(
    ! [B_101,C_21] : k3_zfmisc_1(k1_xboole_0,B_101,C_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_208])).

tff(c_279,plain,(
    ! [B_101,C_21] : k3_zfmisc_1('#skF_3',B_101,C_21) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_275,c_222])).

tff(c_307,plain,(
    ! [B_118] : k2_zfmisc_1('#skF_3',B_118) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_275,c_193])).

tff(c_22,plain,(
    ! [C_18,A_15,B_16] :
      ( v1_xboole_0(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_318,plain,(
    ! [C_18] :
      ( v1_xboole_0(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1('#skF_3'))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_22])).

tff(c_400,plain,(
    ! [C_132] :
      ( v1_xboole_0(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_318])).

tff(c_410,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_400])).

tff(c_54,plain,(
    ! [A_66] :
      ( r2_hidden('#skF_2'(A_66),A_66)
      | k1_xboole_0 = A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_58,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(A_66)
      | k1_xboole_0 = A_66 ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_283,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(A_66)
      | A_66 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_58])).

tff(c_427,plain,(
    '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_410,c_283])).

tff(c_73,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_42,c_2])).

tff(c_431,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_73])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_279,c_431])).

tff(c_440,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_494,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( k5_mcart_1(A_146,B_147,C_148,D_149) = k1_mcart_1(k1_mcart_1(D_149))
      | ~ m1_subset_1(D_149,k3_zfmisc_1(A_146,B_147,C_148))
      | k1_xboole_0 = C_148
      | k1_xboole_0 = B_147
      | k1_xboole_0 = A_146 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_503,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_494])).

tff(c_507,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_503])).

tff(c_844,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_507])).

tff(c_866,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_6])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_664,c_866])).

tff(c_869,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitRight,[status(thm)],[c_507])).

tff(c_871,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_869])).

tff(c_121,plain,(
    ! [A_85,B_86,C_87] : k2_zfmisc_1(k2_zfmisc_1(A_85,B_86),C_87) = k3_zfmisc_1(A_85,B_86,C_87) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden(k1_mcart_1(A_22),B_23)
      | ~ r2_hidden(A_22,k2_zfmisc_1(B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1609,plain,(
    ! [A_231,A_232,B_233,C_234] :
      ( r2_hidden(k1_mcart_1(A_231),k2_zfmisc_1(A_232,B_233))
      | ~ r2_hidden(A_231,k3_zfmisc_1(A_232,B_233,C_234)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_28])).

tff(c_1659,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_42,c_1609])).

tff(c_1670,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1659,c_28])).

tff(c_1679,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_1670])).

tff(c_1681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_1679])).

tff(c_1682,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_869])).

tff(c_26,plain,(
    ! [A_22,C_24,B_23] :
      ( r2_hidden(k2_mcart_1(A_22),C_24)
      | ~ r2_hidden(A_22,k2_zfmisc_1(B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_518,plain,(
    ! [A_153,C_154,A_155,B_156] :
      ( r2_hidden(k2_mcart_1(A_153),C_154)
      | ~ r2_hidden(A_153,k3_zfmisc_1(A_155,B_156,C_154)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_26])).

tff(c_531,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_518])).

tff(c_18,plain,(
    ! [C_12,A_9,B_10] :
      ( r2_hidden(C_12,A_9)
      | ~ r2_hidden(C_12,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_541,plain,(
    ! [A_157] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_157)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_157)) ) ),
    inference(resolution,[status(thm)],[c_531,c_18])).

tff(c_150,plain,(
    ! [A_89,A_13,B_90] :
      ( ~ v1_xboole_0(A_89)
      | ~ r2_hidden(A_13,k2_zfmisc_1(A_89,B_90)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_147])).

tff(c_202,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_150])).

tff(c_219,plain,(
    ! [A_13] : ~ r2_hidden(A_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_202])).

tff(c_565,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_541,c_219])).

tff(c_1692,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1682,c_565])).

tff(c_1709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1692])).

tff(c_1711,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_660])).

tff(c_1721,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1711,c_58])).

tff(c_1742,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_219])).

tff(c_2089,plain,(
    ! [B_259] : v1_xboole_0(k2_zfmisc_1(B_259,'#skF_4')) ),
    inference(resolution,[status(thm)],[c_2056,c_1742])).

tff(c_1710,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_660])).

tff(c_1731,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1710,c_58])).

tff(c_1753,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_1731])).

tff(c_178,plain,(
    ! [A_97,B_98] :
      ( ~ v1_xboole_0(A_97)
      | v1_xboole_0(k2_zfmisc_1(A_97,B_98)) ) ),
    inference(resolution,[status(thm)],[c_4,c_151])).

tff(c_446,plain,(
    ! [A_139,B_140,C_141] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_139,B_140))
      | v1_xboole_0(k3_zfmisc_1(A_139,B_140,C_141)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_178])).

tff(c_462,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_446,c_73])).

tff(c_1755,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1753,c_462])).

tff(c_2100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2089,c_1755])).

tff(c_2102,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2357,plain,(
    ! [A_304] :
      ( r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),A_304)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_304)) ) ),
    inference(resolution,[status(thm)],[c_2102,c_2136])).

tff(c_2256,plain,(
    ! [A_288,B_289,C_290,D_291] :
      ( k7_mcart_1(A_288,B_289,C_290,D_291) = k2_mcart_1(D_291)
      | ~ m1_subset_1(D_291,k3_zfmisc_1(A_288,B_289,C_290))
      | k1_xboole_0 = C_290
      | k1_xboole_0 = B_289
      | k1_xboole_0 = A_288 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2264,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_2256])).

tff(c_2274,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2264])).

tff(c_2157,plain,(
    ! [C_272,A_273,B_274] :
      ( v1_xboole_0(C_272)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274)))
      | ~ v1_xboole_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2164,plain,(
    ! [A_13,A_273,B_274] :
      ( v1_xboole_0(k1_tarski(A_13))
      | ~ v1_xboole_0(A_273)
      | ~ r2_hidden(A_13,k2_zfmisc_1(A_273,B_274)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2157])).

tff(c_2168,plain,(
    ! [A_275,A_276,B_277] :
      ( ~ v1_xboole_0(A_275)
      | ~ r2_hidden(A_276,k2_zfmisc_1(A_275,B_277)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_2164])).

tff(c_2190,plain,(
    ! [A_280,B_281] :
      ( ~ v1_xboole_0(A_280)
      | k2_zfmisc_1(A_280,B_281) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_2168])).

tff(c_2199,plain,(
    ! [B_283] : k2_zfmisc_1(k1_xboole_0,B_283) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2190])).

tff(c_2167,plain,(
    ! [A_273,A_13,B_274] :
      ( ~ v1_xboole_0(A_273)
      | ~ r2_hidden(A_13,k2_zfmisc_1(A_273,B_274)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_2164])).

tff(c_2207,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2199,c_2167])).

tff(c_2224,plain,(
    ! [A_13] : ~ r2_hidden(A_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2207])).

tff(c_2279,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_2224])).

tff(c_2361,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2357,c_2279])).

tff(c_2380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2361])).

tff(c_2381,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_2264])).

tff(c_2730,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2381])).

tff(c_2101,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2107,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2101])).

tff(c_2731,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2730,c_2107])).

tff(c_2734,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2538,c_2731])).

tff(c_2735,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2381])).

tff(c_2737,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2735])).

tff(c_2758,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_6])).

tff(c_2760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2506,c_2758])).

tff(c_2761,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2735])).

tff(c_2548,plain,(
    ! [A_332] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_332)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_332)) ) ),
    inference(resolution,[status(thm)],[c_2538,c_18])).

tff(c_2572,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2548,c_2224])).

tff(c_2766,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2761,c_2572])).

tff(c_2787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2766])).

tff(c_2789,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2502])).

tff(c_2788,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2502])).

tff(c_2866,plain,(
    ! [A_361] :
      ( ~ v1_xboole_0(A_361)
      | A_361 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2788,c_58])).

tff(c_2881,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2789,c_2866])).

tff(c_2893,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_6','#skF_4','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2881,c_42])).

tff(c_3074,plain,(
    ! [A_379,C_380,A_381,B_382] :
      ( r2_hidden(k2_mcart_1(A_379),C_380)
      | ~ r2_hidden(A_379,k3_zfmisc_1(A_381,B_382,C_380)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2125])).

tff(c_3088,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_2893,c_3074])).

tff(c_2826,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_5'
    | k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2788,c_2788,c_2381])).

tff(c_2827,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2826])).

tff(c_3112,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2827,c_2107])).

tff(c_3115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3088,c_3112])).

tff(c_3116,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2826])).

tff(c_3162,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3116])).

tff(c_3198,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3162,c_2788])).

tff(c_2135,plain,(
    ! [B_266,C_265] :
      ( r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_266,C_265))),C_265)
      | k2_zfmisc_1(B_266,C_265) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_2125])).

tff(c_3824,plain,(
    ! [B_452,C_453] :
      ( r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_452,C_453))),C_453)
      | k2_zfmisc_1(B_452,C_453) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3198,c_2135])).

tff(c_2816,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2788,c_2224])).

tff(c_3194,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3162,c_2816])).

tff(c_3862,plain,(
    ! [B_452] : k2_zfmisc_1(B_452,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3824,c_3194])).

tff(c_2182,plain,(
    ! [A_278,B_279] :
      ( ~ v1_xboole_0(A_278)
      | v1_xboole_0(k2_zfmisc_1(A_278,B_279)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2168])).

tff(c_2383,plain,(
    ! [A_305,B_306,C_307] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_305,B_306))
      | v1_xboole_0(k3_zfmisc_1(A_305,B_306,C_307)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2182])).

tff(c_2399,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2383,c_73])).

tff(c_3199,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3162,c_2399])).

tff(c_3870,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_3199])).

tff(c_3873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2789,c_3870])).

tff(c_3874,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3116])).

tff(c_2821,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2788,c_6])).

tff(c_3879,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3874,c_2821])).

tff(c_3888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2504,c_3879])).

tff(c_3889,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2501])).

tff(c_3902,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3889,c_2224])).

tff(c_4213,plain,(
    ! [A_489,C_490,A_491,B_492] :
      ( r2_hidden(k2_mcart_1(A_489),C_490)
      | ~ r2_hidden(A_489,k3_zfmisc_1(A_491,B_492,C_490)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2125])).

tff(c_4225,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_4213])).

tff(c_4234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3902,c_4225])).

tff(c_4235,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2101])).

tff(c_4310,plain,(
    ! [C_509,A_510,B_511] :
      ( r2_hidden(C_509,A_510)
      | ~ r2_hidden(C_509,B_511)
      | ~ m1_subset_1(B_511,k1_zfmisc_1(A_510)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4688,plain,(
    ! [A_561,A_562] :
      ( r2_hidden('#skF_2'(A_561),A_562)
      | ~ m1_subset_1(A_561,k1_zfmisc_1(A_562))
      | k1_xboole_0 = A_561 ) ),
    inference(resolution,[status(thm)],[c_38,c_4310])).

tff(c_4738,plain,(
    ! [A_568,A_569] :
      ( ~ v1_xboole_0(A_568)
      | ~ m1_subset_1(A_569,k1_zfmisc_1(A_568))
      | k1_xboole_0 = A_569 ) ),
    inference(resolution,[status(thm)],[c_4688,c_2])).

tff(c_4753,plain,
    ( ~ v1_xboole_0('#skF_4')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_48,c_4738])).

tff(c_4755,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4753])).

tff(c_4526,plain,(
    ! [A_539] :
      ( r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),A_539)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_539)) ) ),
    inference(resolution,[status(thm)],[c_2102,c_4310])).

tff(c_4396,plain,(
    ! [A_521,B_522,C_523,D_524] :
      ( k7_mcart_1(A_521,B_522,C_523,D_524) = k2_mcart_1(D_524)
      | ~ m1_subset_1(D_524,k3_zfmisc_1(A_521,B_522,C_523))
      | k1_xboole_0 = C_523
      | k1_xboole_0 = B_522
      | k1_xboole_0 = A_521 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4404,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_4396])).

tff(c_4434,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4404])).

tff(c_4269,plain,(
    ! [C_499,A_500,B_501] :
      ( v1_xboole_0(C_499)
      | ~ m1_subset_1(C_499,k1_zfmisc_1(k2_zfmisc_1(A_500,B_501)))
      | ~ v1_xboole_0(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4276,plain,(
    ! [A_13,A_500,B_501] :
      ( v1_xboole_0(k1_tarski(A_13))
      | ~ v1_xboole_0(A_500)
      | ~ r2_hidden(A_13,k2_zfmisc_1(A_500,B_501)) ) ),
    inference(resolution,[status(thm)],[c_20,c_4269])).

tff(c_4280,plain,(
    ! [A_502,A_503,B_504] :
      ( ~ v1_xboole_0(A_502)
      | ~ r2_hidden(A_503,k2_zfmisc_1(A_502,B_504)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_4276])).

tff(c_4302,plain,(
    ! [A_507,B_508] :
      ( ~ v1_xboole_0(A_507)
      | k2_zfmisc_1(A_507,B_508) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_4280])).

tff(c_4329,plain,(
    ! [B_512] : k2_zfmisc_1(k1_xboole_0,B_512) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_4302])).

tff(c_4279,plain,(
    ! [A_500,A_13,B_501] :
      ( ~ v1_xboole_0(A_500)
      | ~ r2_hidden(A_13,k2_zfmisc_1(A_500,B_501)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_4276])).

tff(c_4337,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4329,c_4279])).

tff(c_4354,plain,(
    ! [A_13] : ~ r2_hidden(A_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4337])).

tff(c_4439,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4434,c_4354])).

tff(c_4530,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4526,c_4439])).

tff(c_4549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4530])).

tff(c_4551,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4404])).

tff(c_4616,plain,(
    ! [A_553,B_554,C_555,D_556] :
      ( k5_mcart_1(A_553,B_554,C_555,D_556) = k1_mcart_1(k1_mcart_1(D_556))
      | ~ m1_subset_1(D_556,k3_zfmisc_1(A_553,B_554,C_555))
      | k1_xboole_0 = C_555
      | k1_xboole_0 = B_554
      | k1_xboole_0 = A_553 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4625,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_4616])).

tff(c_4629,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_4551,c_4625])).

tff(c_5312,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4629])).

tff(c_5339,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5312,c_6])).

tff(c_5341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4755,c_5339])).

tff(c_5343,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4629])).

tff(c_4718,plain,(
    ! [A_563,B_564,C_565,D_566] :
      ( k6_mcart_1(A_563,B_564,C_565,D_566) = k2_mcart_1(k1_mcart_1(D_566))
      | ~ m1_subset_1(D_566,k3_zfmisc_1(A_563,B_564,C_565))
      | k1_xboole_0 = C_565
      | k1_xboole_0 = B_564
      | k1_xboole_0 = A_563 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4727,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_4718])).

tff(c_4731,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_4551,c_4727])).

tff(c_5535,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_5343,c_4731])).

tff(c_5536,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5535])).

tff(c_4258,plain,(
    ! [A_496,C_497,B_498] :
      ( r2_hidden(k2_mcart_1(A_496),C_497)
      | ~ r2_hidden(A_496,k2_zfmisc_1(B_498,C_497)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4600,plain,(
    ! [A_549,C_550,A_551,B_552] :
      ( r2_hidden(k2_mcart_1(A_549),C_550)
      | ~ r2_hidden(A_549,k3_zfmisc_1(A_551,B_552,C_550)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4258])).

tff(c_4613,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_4600])).

tff(c_4637,plain,(
    ! [A_557] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_557)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_557)) ) ),
    inference(resolution,[status(thm)],[c_4613,c_18])).

tff(c_4661,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4637,c_4354])).

tff(c_5553,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5536,c_4661])).

tff(c_5570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5553])).

tff(c_5571,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitRight,[status(thm)],[c_5535])).

tff(c_4241,plain,(
    ! [A_493,B_494,C_495] : k2_zfmisc_1(k2_zfmisc_1(A_493,B_494),C_495) = k3_zfmisc_1(A_493,B_494,C_495) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_9170,plain,(
    ! [A_729,A_730,B_731,C_732] :
      ( r2_hidden(k1_mcart_1(A_729),k2_zfmisc_1(A_730,B_731))
      | ~ r2_hidden(A_729,k3_zfmisc_1(A_730,B_731,C_732)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4241,c_28])).

tff(c_9246,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_42,c_9170])).

tff(c_9255,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_9246,c_26])).

tff(c_9264,plain,(
    r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5571,c_9255])).

tff(c_9266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4235,c_9264])).

tff(c_9268,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4753])).

tff(c_9267,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4753])).

tff(c_9352,plain,(
    ! [A_741] :
      ( ~ v1_xboole_0(A_741)
      | A_741 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9267,c_58])).

tff(c_9367,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9268,c_9352])).

tff(c_9376,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9367,c_9267])).

tff(c_4268,plain,(
    ! [B_498,C_497] :
      ( r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_498,C_497))),C_497)
      | k2_zfmisc_1(B_498,C_497) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_4258])).

tff(c_9672,plain,(
    ! [B_763,C_764] :
      ( r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_763,C_764))),C_764)
      | k2_zfmisc_1(B_763,C_764) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9376,c_4268])).

tff(c_9282,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9267,c_4354])).

tff(c_9373,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9367,c_9282])).

tff(c_9701,plain,(
    ! [B_763] : k2_zfmisc_1(B_763,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9672,c_9373])).

tff(c_4294,plain,(
    ! [A_505,B_506] :
      ( ~ v1_xboole_0(A_505)
      | v1_xboole_0(k2_zfmisc_1(A_505,B_506)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4280])).

tff(c_4410,plain,(
    ! [A_527,B_528,C_529] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_527,B_528))
      | v1_xboole_0(k3_zfmisc_1(A_527,B_528,C_529)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4294])).

tff(c_4426,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4410,c_73])).

tff(c_9377,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9367,c_4426])).

tff(c_9710,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9701,c_9377])).

tff(c_9713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9268,c_9710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:53:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.60/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.60/2.33  
% 6.60/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.60/2.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4
% 6.60/2.34  
% 6.60/2.34  %Foreground sorts:
% 6.60/2.34  
% 6.60/2.34  
% 6.60/2.34  %Background operators:
% 6.60/2.34  
% 6.60/2.34  
% 6.60/2.34  %Foreground operators:
% 6.60/2.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.60/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.60/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.60/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.60/2.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.60/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.60/2.34  tff('#skF_7', type, '#skF_7': $i).
% 6.60/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.60/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.60/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.60/2.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.60/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.60/2.34  tff('#skF_9', type, '#skF_9': $i).
% 6.60/2.34  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 6.60/2.34  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.60/2.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.60/2.34  tff('#skF_8', type, '#skF_8': $i).
% 6.60/2.34  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 6.60/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.60/2.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.60/2.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.60/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.60/2.34  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 6.60/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.60/2.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.60/2.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.60/2.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.60/2.34  
% 6.60/2.37  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 6.60/2.37  tff(f_109, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 6.60/2.37  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.60/2.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.60/2.37  tff(f_62, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 6.60/2.37  tff(f_68, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 6.60/2.37  tff(f_88, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 6.60/2.37  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.60/2.37  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.60/2.37  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.60/2.37  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 6.60/2.37  tff(f_60, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 6.60/2.37  tff(c_46, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.60/2.37  tff(c_38, plain, (![A_30]: (r2_hidden('#skF_2'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.60/2.37  tff(c_2136, plain, (![C_267, A_268, B_269]: (r2_hidden(C_267, A_268) | ~r2_hidden(C_267, B_269) | ~m1_subset_1(B_269, k1_zfmisc_1(A_268)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.60/2.37  tff(c_2455, plain, (![A_319, A_320]: (r2_hidden('#skF_2'(A_319), A_320) | ~m1_subset_1(A_319, k1_zfmisc_1(A_320)) | k1_xboole_0=A_319)), inference(resolution, [status(thm)], [c_38, c_2136])).
% 6.60/2.37  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.60/2.37  tff(c_2487, plain, (![A_322, A_323]: (~v1_xboole_0(A_322) | ~m1_subset_1(A_323, k1_zfmisc_1(A_322)) | k1_xboole_0=A_323)), inference(resolution, [status(thm)], [c_2455, c_2])).
% 6.60/2.37  tff(c_2501, plain, (~v1_xboole_0('#skF_5') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_46, c_2487])).
% 6.60/2.37  tff(c_2504, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_2501])).
% 6.60/2.37  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.60/2.37  tff(c_2502, plain, (~v1_xboole_0('#skF_4') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_48, c_2487])).
% 6.60/2.37  tff(c_2506, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2502])).
% 6.60/2.37  tff(c_42, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.60/2.37  tff(c_24, plain, (![A_19, B_20, C_21]: (k2_zfmisc_1(k2_zfmisc_1(A_19, B_20), C_21)=k3_zfmisc_1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.60/2.37  tff(c_2125, plain, (![A_264, C_265, B_266]: (r2_hidden(k2_mcart_1(A_264), C_265) | ~r2_hidden(A_264, k2_zfmisc_1(B_266, C_265)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.60/2.37  tff(c_2521, plain, (![A_328, C_329, A_330, B_331]: (r2_hidden(k2_mcart_1(A_328), C_329) | ~r2_hidden(A_328, k3_zfmisc_1(A_330, B_331, C_329)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2125])).
% 6.60/2.37  tff(c_2538, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_42, c_2521])).
% 6.60/2.37  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.60/2.37  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.60/2.37  tff(c_112, plain, (![A_82, C_83, B_84]: (r2_hidden(k2_mcart_1(A_82), C_83) | ~r2_hidden(A_82, k2_zfmisc_1(B_84, C_83)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.60/2.37  tff(c_2056, plain, (![B_259, C_260]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_259, C_260))), C_260) | v1_xboole_0(k2_zfmisc_1(B_259, C_260)))), inference(resolution, [status(thm)], [c_4, c_112])).
% 6.60/2.37  tff(c_40, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8') | ~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.60/2.37  tff(c_111, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_40])).
% 6.60/2.37  tff(c_165, plain, (![C_94, A_95, B_96]: (r2_hidden(C_94, A_95) | ~r2_hidden(C_94, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.60/2.37  tff(c_613, plain, (![A_167, A_168]: (r2_hidden('#skF_1'(A_167), A_168) | ~m1_subset_1(A_167, k1_zfmisc_1(A_168)) | v1_xboole_0(A_167))), inference(resolution, [status(thm)], [c_4, c_165])).
% 6.60/2.37  tff(c_643, plain, (![A_169, A_170]: (~v1_xboole_0(A_169) | ~m1_subset_1(A_170, k1_zfmisc_1(A_169)) | v1_xboole_0(A_170))), inference(resolution, [status(thm)], [c_613, c_2])).
% 6.60/2.37  tff(c_660, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_48, c_643])).
% 6.60/2.37  tff(c_664, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_660])).
% 6.60/2.37  tff(c_44, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.60/2.37  tff(c_260, plain, (![A_110, B_111, C_112, D_113]: (k7_mcart_1(A_110, B_111, C_112, D_113)=k2_mcart_1(D_113) | ~m1_subset_1(D_113, k3_zfmisc_1(A_110, B_111, C_112)) | k1_xboole_0=C_112 | k1_xboole_0=B_111 | k1_xboole_0=A_110)), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.60/2.37  tff(c_268, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44, c_260])).
% 6.60/2.37  tff(c_275, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_268])).
% 6.60/2.37  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.60/2.37  tff(c_285, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_6])).
% 6.60/2.37  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.60/2.37  tff(c_75, plain, (![A_71, B_72]: (r2_hidden(A_71, B_72) | ~r1_tarski(k1_tarski(A_71), B_72))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.60/2.37  tff(c_85, plain, (![A_73]: (r2_hidden(A_73, k1_tarski(A_73)))), inference(resolution, [status(thm)], [c_12, c_75])).
% 6.60/2.37  tff(c_89, plain, (![A_73]: (~v1_xboole_0(k1_tarski(A_73)))), inference(resolution, [status(thm)], [c_85, c_2])).
% 6.60/2.37  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(k1_tarski(A_13), k1_zfmisc_1(B_14)) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.60/2.37  tff(c_140, plain, (![C_88, A_89, B_90]: (v1_xboole_0(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.60/2.37  tff(c_147, plain, (![A_13, A_89, B_90]: (v1_xboole_0(k1_tarski(A_13)) | ~v1_xboole_0(A_89) | ~r2_hidden(A_13, k2_zfmisc_1(A_89, B_90)))), inference(resolution, [status(thm)], [c_20, c_140])).
% 6.60/2.37  tff(c_151, plain, (![A_91, A_92, B_93]: (~v1_xboole_0(A_91) | ~r2_hidden(A_92, k2_zfmisc_1(A_91, B_93)))), inference(negUnitSimplification, [status(thm)], [c_89, c_147])).
% 6.60/2.37  tff(c_186, plain, (![A_99, B_100]: (~v1_xboole_0(A_99) | k2_zfmisc_1(A_99, B_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_151])).
% 6.60/2.37  tff(c_193, plain, (![B_100]: (k2_zfmisc_1(k1_xboole_0, B_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_186])).
% 6.60/2.37  tff(c_194, plain, (![B_101]: (k2_zfmisc_1(k1_xboole_0, B_101)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_186])).
% 6.60/2.37  tff(c_208, plain, (![B_101, C_21]: (k3_zfmisc_1(k1_xboole_0, B_101, C_21)=k2_zfmisc_1(k1_xboole_0, C_21))), inference(superposition, [status(thm), theory('equality')], [c_194, c_24])).
% 6.60/2.37  tff(c_222, plain, (![B_101, C_21]: (k3_zfmisc_1(k1_xboole_0, B_101, C_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_193, c_208])).
% 6.60/2.37  tff(c_279, plain, (![B_101, C_21]: (k3_zfmisc_1('#skF_3', B_101, C_21)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_275, c_222])).
% 6.60/2.37  tff(c_307, plain, (![B_118]: (k2_zfmisc_1('#skF_3', B_118)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_275, c_193])).
% 6.60/2.37  tff(c_22, plain, (![C_18, A_15, B_16]: (v1_xboole_0(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.60/2.37  tff(c_318, plain, (![C_18]: (v1_xboole_0(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1('#skF_3')) | ~v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_22])).
% 6.60/2.37  tff(c_400, plain, (![C_132]: (v1_xboole_0(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_318])).
% 6.60/2.37  tff(c_410, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_50, c_400])).
% 6.60/2.37  tff(c_54, plain, (![A_66]: (r2_hidden('#skF_2'(A_66), A_66) | k1_xboole_0=A_66)), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.60/2.37  tff(c_58, plain, (![A_66]: (~v1_xboole_0(A_66) | k1_xboole_0=A_66)), inference(resolution, [status(thm)], [c_54, c_2])).
% 6.60/2.37  tff(c_283, plain, (![A_66]: (~v1_xboole_0(A_66) | A_66='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_58])).
% 6.60/2.37  tff(c_427, plain, ('#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_410, c_283])).
% 6.60/2.37  tff(c_73, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_42, c_2])).
% 6.60/2.37  tff(c_431, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_427, c_73])).
% 6.60/2.37  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_285, c_279, c_431])).
% 6.60/2.37  tff(c_440, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_268])).
% 6.60/2.37  tff(c_494, plain, (![A_146, B_147, C_148, D_149]: (k5_mcart_1(A_146, B_147, C_148, D_149)=k1_mcart_1(k1_mcart_1(D_149)) | ~m1_subset_1(D_149, k3_zfmisc_1(A_146, B_147, C_148)) | k1_xboole_0=C_148 | k1_xboole_0=B_147 | k1_xboole_0=A_146)), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.60/2.37  tff(c_503, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44, c_494])).
% 6.60/2.37  tff(c_507, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_440, c_503])).
% 6.60/2.37  tff(c_844, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_507])).
% 6.60/2.37  tff(c_866, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_844, c_6])).
% 6.60/2.37  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_664, c_866])).
% 6.60/2.37  tff(c_869, plain, (k1_xboole_0='#skF_5' | k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitRight, [status(thm)], [c_507])).
% 6.60/2.37  tff(c_871, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitLeft, [status(thm)], [c_869])).
% 6.60/2.37  tff(c_121, plain, (![A_85, B_86, C_87]: (k2_zfmisc_1(k2_zfmisc_1(A_85, B_86), C_87)=k3_zfmisc_1(A_85, B_86, C_87))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.60/2.37  tff(c_28, plain, (![A_22, B_23, C_24]: (r2_hidden(k1_mcart_1(A_22), B_23) | ~r2_hidden(A_22, k2_zfmisc_1(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.60/2.37  tff(c_1609, plain, (![A_231, A_232, B_233, C_234]: (r2_hidden(k1_mcart_1(A_231), k2_zfmisc_1(A_232, B_233)) | ~r2_hidden(A_231, k3_zfmisc_1(A_232, B_233, C_234)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_28])).
% 6.60/2.37  tff(c_1659, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_1609])).
% 6.60/2.37  tff(c_1670, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_6')), inference(resolution, [status(thm)], [c_1659, c_28])).
% 6.60/2.37  tff(c_1679, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_871, c_1670])).
% 6.60/2.37  tff(c_1681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_1679])).
% 6.60/2.37  tff(c_1682, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_869])).
% 6.60/2.37  tff(c_26, plain, (![A_22, C_24, B_23]: (r2_hidden(k2_mcart_1(A_22), C_24) | ~r2_hidden(A_22, k2_zfmisc_1(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.60/2.37  tff(c_518, plain, (![A_153, C_154, A_155, B_156]: (r2_hidden(k2_mcart_1(A_153), C_154) | ~r2_hidden(A_153, k3_zfmisc_1(A_155, B_156, C_154)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_26])).
% 6.60/2.37  tff(c_531, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_42, c_518])).
% 6.60/2.37  tff(c_18, plain, (![C_12, A_9, B_10]: (r2_hidden(C_12, A_9) | ~r2_hidden(C_12, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.60/2.37  tff(c_541, plain, (![A_157]: (r2_hidden(k2_mcart_1('#skF_9'), A_157) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_157)))), inference(resolution, [status(thm)], [c_531, c_18])).
% 6.60/2.37  tff(c_150, plain, (![A_89, A_13, B_90]: (~v1_xboole_0(A_89) | ~r2_hidden(A_13, k2_zfmisc_1(A_89, B_90)))), inference(negUnitSimplification, [status(thm)], [c_89, c_147])).
% 6.60/2.37  tff(c_202, plain, (![A_13]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_194, c_150])).
% 6.60/2.37  tff(c_219, plain, (![A_13]: (~r2_hidden(A_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_202])).
% 6.60/2.37  tff(c_565, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_541, c_219])).
% 6.60/2.37  tff(c_1692, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1682, c_565])).
% 6.60/2.37  tff(c_1709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1692])).
% 6.60/2.37  tff(c_1711, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_660])).
% 6.60/2.37  tff(c_1721, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1711, c_58])).
% 6.60/2.37  tff(c_1742, plain, (![A_13]: (~r2_hidden(A_13, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_219])).
% 6.60/2.37  tff(c_2089, plain, (![B_259]: (v1_xboole_0(k2_zfmisc_1(B_259, '#skF_4')))), inference(resolution, [status(thm)], [c_2056, c_1742])).
% 6.60/2.37  tff(c_1710, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_660])).
% 6.60/2.37  tff(c_1731, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1710, c_58])).
% 6.60/2.37  tff(c_1753, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_1731])).
% 6.60/2.37  tff(c_178, plain, (![A_97, B_98]: (~v1_xboole_0(A_97) | v1_xboole_0(k2_zfmisc_1(A_97, B_98)))), inference(resolution, [status(thm)], [c_4, c_151])).
% 6.60/2.37  tff(c_446, plain, (![A_139, B_140, C_141]: (~v1_xboole_0(k2_zfmisc_1(A_139, B_140)) | v1_xboole_0(k3_zfmisc_1(A_139, B_140, C_141)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_178])).
% 6.60/2.37  tff(c_462, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_446, c_73])).
% 6.60/2.37  tff(c_1755, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1753, c_462])).
% 6.60/2.37  tff(c_2100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2089, c_1755])).
% 6.60/2.37  tff(c_2102, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_40])).
% 6.60/2.37  tff(c_2357, plain, (![A_304]: (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), A_304) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_304)))), inference(resolution, [status(thm)], [c_2102, c_2136])).
% 6.60/2.37  tff(c_2256, plain, (![A_288, B_289, C_290, D_291]: (k7_mcart_1(A_288, B_289, C_290, D_291)=k2_mcart_1(D_291) | ~m1_subset_1(D_291, k3_zfmisc_1(A_288, B_289, C_290)) | k1_xboole_0=C_290 | k1_xboole_0=B_289 | k1_xboole_0=A_288)), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.60/2.37  tff(c_2264, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44, c_2256])).
% 6.60/2.37  tff(c_2274, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2264])).
% 6.60/2.37  tff(c_2157, plain, (![C_272, A_273, B_274]: (v1_xboole_0(C_272) | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))) | ~v1_xboole_0(A_273))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.60/2.37  tff(c_2164, plain, (![A_13, A_273, B_274]: (v1_xboole_0(k1_tarski(A_13)) | ~v1_xboole_0(A_273) | ~r2_hidden(A_13, k2_zfmisc_1(A_273, B_274)))), inference(resolution, [status(thm)], [c_20, c_2157])).
% 6.60/2.37  tff(c_2168, plain, (![A_275, A_276, B_277]: (~v1_xboole_0(A_275) | ~r2_hidden(A_276, k2_zfmisc_1(A_275, B_277)))), inference(negUnitSimplification, [status(thm)], [c_89, c_2164])).
% 6.60/2.37  tff(c_2190, plain, (![A_280, B_281]: (~v1_xboole_0(A_280) | k2_zfmisc_1(A_280, B_281)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_2168])).
% 6.60/2.37  tff(c_2199, plain, (![B_283]: (k2_zfmisc_1(k1_xboole_0, B_283)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_2190])).
% 6.60/2.37  tff(c_2167, plain, (![A_273, A_13, B_274]: (~v1_xboole_0(A_273) | ~r2_hidden(A_13, k2_zfmisc_1(A_273, B_274)))), inference(negUnitSimplification, [status(thm)], [c_89, c_2164])).
% 6.60/2.37  tff(c_2207, plain, (![A_13]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2199, c_2167])).
% 6.60/2.37  tff(c_2224, plain, (![A_13]: (~r2_hidden(A_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2207])).
% 6.60/2.37  tff(c_2279, plain, (![A_13]: (~r2_hidden(A_13, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_2224])).
% 6.60/2.37  tff(c_2361, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_2357, c_2279])).
% 6.60/2.37  tff(c_2380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_2361])).
% 6.60/2.37  tff(c_2381, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitRight, [status(thm)], [c_2264])).
% 6.60/2.37  tff(c_2730, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitLeft, [status(thm)], [c_2381])).
% 6.60/2.37  tff(c_2101, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_40])).
% 6.60/2.37  tff(c_2107, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_2101])).
% 6.60/2.37  tff(c_2731, plain, (~r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2730, c_2107])).
% 6.60/2.37  tff(c_2734, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2538, c_2731])).
% 6.60/2.37  tff(c_2735, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2381])).
% 6.60/2.37  tff(c_2737, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2735])).
% 6.60/2.37  tff(c_2758, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_6])).
% 6.60/2.37  tff(c_2760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2506, c_2758])).
% 6.60/2.37  tff(c_2761, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2735])).
% 6.60/2.37  tff(c_2548, plain, (![A_332]: (r2_hidden(k2_mcart_1('#skF_9'), A_332) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_332)))), inference(resolution, [status(thm)], [c_2538, c_18])).
% 6.60/2.37  tff(c_2572, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2548, c_2224])).
% 6.60/2.37  tff(c_2766, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2761, c_2572])).
% 6.60/2.37  tff(c_2787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2766])).
% 6.60/2.37  tff(c_2789, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_2502])).
% 6.60/2.37  tff(c_2788, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2502])).
% 6.60/2.37  tff(c_2866, plain, (![A_361]: (~v1_xboole_0(A_361) | A_361='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2788, c_58])).
% 6.60/2.37  tff(c_2881, plain, ('#skF_7'='#skF_4'), inference(resolution, [status(thm)], [c_2789, c_2866])).
% 6.60/2.37  tff(c_2893, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_6', '#skF_4', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2881, c_42])).
% 6.60/2.37  tff(c_3074, plain, (![A_379, C_380, A_381, B_382]: (r2_hidden(k2_mcart_1(A_379), C_380) | ~r2_hidden(A_379, k3_zfmisc_1(A_381, B_382, C_380)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2125])).
% 6.60/2.37  tff(c_3088, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_2893, c_3074])).
% 6.60/2.37  tff(c_2826, plain, ('#skF_7'='#skF_4' | '#skF_7'='#skF_5' | k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2788, c_2788, c_2381])).
% 6.60/2.37  tff(c_2827, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitLeft, [status(thm)], [c_2826])).
% 6.60/2.37  tff(c_3112, plain, (~r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2827, c_2107])).
% 6.60/2.37  tff(c_3115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3088, c_3112])).
% 6.60/2.37  tff(c_3116, plain, ('#skF_7'='#skF_5' | '#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_2826])).
% 6.60/2.37  tff(c_3162, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_3116])).
% 6.60/2.37  tff(c_3198, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3162, c_2788])).
% 6.60/2.37  tff(c_2135, plain, (![B_266, C_265]: (r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_266, C_265))), C_265) | k2_zfmisc_1(B_266, C_265)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_2125])).
% 6.60/2.37  tff(c_3824, plain, (![B_452, C_453]: (r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_452, C_453))), C_453) | k2_zfmisc_1(B_452, C_453)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3198, c_2135])).
% 6.60/2.37  tff(c_2816, plain, (![A_13]: (~r2_hidden(A_13, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2788, c_2224])).
% 6.60/2.37  tff(c_3194, plain, (![A_13]: (~r2_hidden(A_13, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3162, c_2816])).
% 6.60/2.37  tff(c_3862, plain, (![B_452]: (k2_zfmisc_1(B_452, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_3824, c_3194])).
% 6.60/2.37  tff(c_2182, plain, (![A_278, B_279]: (~v1_xboole_0(A_278) | v1_xboole_0(k2_zfmisc_1(A_278, B_279)))), inference(resolution, [status(thm)], [c_4, c_2168])).
% 6.60/2.37  tff(c_2383, plain, (![A_305, B_306, C_307]: (~v1_xboole_0(k2_zfmisc_1(A_305, B_306)) | v1_xboole_0(k3_zfmisc_1(A_305, B_306, C_307)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2182])).
% 6.60/2.37  tff(c_2399, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_2383, c_73])).
% 6.60/2.37  tff(c_3199, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3162, c_2399])).
% 6.60/2.37  tff(c_3870, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3862, c_3199])).
% 6.60/2.37  tff(c_3873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2789, c_3870])).
% 6.60/2.37  tff(c_3874, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_3116])).
% 6.60/2.37  tff(c_2821, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2788, c_6])).
% 6.60/2.37  tff(c_3879, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3874, c_2821])).
% 6.60/2.37  tff(c_3888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2504, c_3879])).
% 6.60/2.37  tff(c_3889, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_2501])).
% 6.60/2.37  tff(c_3902, plain, (![A_13]: (~r2_hidden(A_13, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3889, c_2224])).
% 6.60/2.37  tff(c_4213, plain, (![A_489, C_490, A_491, B_492]: (r2_hidden(k2_mcart_1(A_489), C_490) | ~r2_hidden(A_489, k3_zfmisc_1(A_491, B_492, C_490)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2125])).
% 6.60/2.37  tff(c_4225, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_42, c_4213])).
% 6.60/2.37  tff(c_4234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3902, c_4225])).
% 6.60/2.37  tff(c_4235, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_2101])).
% 6.60/2.37  tff(c_4310, plain, (![C_509, A_510, B_511]: (r2_hidden(C_509, A_510) | ~r2_hidden(C_509, B_511) | ~m1_subset_1(B_511, k1_zfmisc_1(A_510)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.60/2.37  tff(c_4688, plain, (![A_561, A_562]: (r2_hidden('#skF_2'(A_561), A_562) | ~m1_subset_1(A_561, k1_zfmisc_1(A_562)) | k1_xboole_0=A_561)), inference(resolution, [status(thm)], [c_38, c_4310])).
% 6.60/2.37  tff(c_4738, plain, (![A_568, A_569]: (~v1_xboole_0(A_568) | ~m1_subset_1(A_569, k1_zfmisc_1(A_568)) | k1_xboole_0=A_569)), inference(resolution, [status(thm)], [c_4688, c_2])).
% 6.60/2.37  tff(c_4753, plain, (~v1_xboole_0('#skF_4') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_48, c_4738])).
% 6.60/2.37  tff(c_4755, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_4753])).
% 6.60/2.37  tff(c_4526, plain, (![A_539]: (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), A_539) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_539)))), inference(resolution, [status(thm)], [c_2102, c_4310])).
% 6.60/2.37  tff(c_4396, plain, (![A_521, B_522, C_523, D_524]: (k7_mcart_1(A_521, B_522, C_523, D_524)=k2_mcart_1(D_524) | ~m1_subset_1(D_524, k3_zfmisc_1(A_521, B_522, C_523)) | k1_xboole_0=C_523 | k1_xboole_0=B_522 | k1_xboole_0=A_521)), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.60/2.37  tff(c_4404, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44, c_4396])).
% 6.60/2.37  tff(c_4434, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4404])).
% 6.60/2.37  tff(c_4269, plain, (![C_499, A_500, B_501]: (v1_xboole_0(C_499) | ~m1_subset_1(C_499, k1_zfmisc_1(k2_zfmisc_1(A_500, B_501))) | ~v1_xboole_0(A_500))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.60/2.37  tff(c_4276, plain, (![A_13, A_500, B_501]: (v1_xboole_0(k1_tarski(A_13)) | ~v1_xboole_0(A_500) | ~r2_hidden(A_13, k2_zfmisc_1(A_500, B_501)))), inference(resolution, [status(thm)], [c_20, c_4269])).
% 6.60/2.37  tff(c_4280, plain, (![A_502, A_503, B_504]: (~v1_xboole_0(A_502) | ~r2_hidden(A_503, k2_zfmisc_1(A_502, B_504)))), inference(negUnitSimplification, [status(thm)], [c_89, c_4276])).
% 6.60/2.37  tff(c_4302, plain, (![A_507, B_508]: (~v1_xboole_0(A_507) | k2_zfmisc_1(A_507, B_508)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_4280])).
% 6.60/2.37  tff(c_4329, plain, (![B_512]: (k2_zfmisc_1(k1_xboole_0, B_512)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_4302])).
% 6.60/2.37  tff(c_4279, plain, (![A_500, A_13, B_501]: (~v1_xboole_0(A_500) | ~r2_hidden(A_13, k2_zfmisc_1(A_500, B_501)))), inference(negUnitSimplification, [status(thm)], [c_89, c_4276])).
% 6.60/2.37  tff(c_4337, plain, (![A_13]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4329, c_4279])).
% 6.60/2.37  tff(c_4354, plain, (![A_13]: (~r2_hidden(A_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4337])).
% 6.60/2.37  tff(c_4439, plain, (![A_13]: (~r2_hidden(A_13, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4434, c_4354])).
% 6.60/2.37  tff(c_4530, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_4526, c_4439])).
% 6.60/2.37  tff(c_4549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_4530])).
% 6.60/2.37  tff(c_4551, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4404])).
% 6.60/2.37  tff(c_4616, plain, (![A_553, B_554, C_555, D_556]: (k5_mcart_1(A_553, B_554, C_555, D_556)=k1_mcart_1(k1_mcart_1(D_556)) | ~m1_subset_1(D_556, k3_zfmisc_1(A_553, B_554, C_555)) | k1_xboole_0=C_555 | k1_xboole_0=B_554 | k1_xboole_0=A_553)), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.60/2.37  tff(c_4625, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44, c_4616])).
% 6.60/2.37  tff(c_4629, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_4551, c_4625])).
% 6.60/2.37  tff(c_5312, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_4629])).
% 6.60/2.37  tff(c_5339, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5312, c_6])).
% 6.60/2.37  tff(c_5341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4755, c_5339])).
% 6.60/2.37  tff(c_5343, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_4629])).
% 6.60/2.37  tff(c_4718, plain, (![A_563, B_564, C_565, D_566]: (k6_mcart_1(A_563, B_564, C_565, D_566)=k2_mcart_1(k1_mcart_1(D_566)) | ~m1_subset_1(D_566, k3_zfmisc_1(A_563, B_564, C_565)) | k1_xboole_0=C_565 | k1_xboole_0=B_564 | k1_xboole_0=A_563)), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.60/2.37  tff(c_4727, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_44, c_4718])).
% 6.60/2.37  tff(c_4731, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_4551, c_4727])).
% 6.60/2.37  tff(c_5535, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_5343, c_4731])).
% 6.60/2.37  tff(c_5536, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_5535])).
% 6.60/2.37  tff(c_4258, plain, (![A_496, C_497, B_498]: (r2_hidden(k2_mcart_1(A_496), C_497) | ~r2_hidden(A_496, k2_zfmisc_1(B_498, C_497)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.60/2.37  tff(c_4600, plain, (![A_549, C_550, A_551, B_552]: (r2_hidden(k2_mcart_1(A_549), C_550) | ~r2_hidden(A_549, k3_zfmisc_1(A_551, B_552, C_550)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4258])).
% 6.60/2.37  tff(c_4613, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_42, c_4600])).
% 6.60/2.37  tff(c_4637, plain, (![A_557]: (r2_hidden(k2_mcart_1('#skF_9'), A_557) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_557)))), inference(resolution, [status(thm)], [c_4613, c_18])).
% 6.60/2.37  tff(c_4661, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4637, c_4354])).
% 6.60/2.37  tff(c_5553, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5536, c_4661])).
% 6.60/2.37  tff(c_5570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_5553])).
% 6.60/2.37  tff(c_5571, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitRight, [status(thm)], [c_5535])).
% 6.60/2.37  tff(c_4241, plain, (![A_493, B_494, C_495]: (k2_zfmisc_1(k2_zfmisc_1(A_493, B_494), C_495)=k3_zfmisc_1(A_493, B_494, C_495))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.60/2.37  tff(c_9170, plain, (![A_729, A_730, B_731, C_732]: (r2_hidden(k1_mcart_1(A_729), k2_zfmisc_1(A_730, B_731)) | ~r2_hidden(A_729, k3_zfmisc_1(A_730, B_731, C_732)))), inference(superposition, [status(thm), theory('equality')], [c_4241, c_28])).
% 6.60/2.37  tff(c_9246, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_9170])).
% 6.60/2.37  tff(c_9255, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_9246, c_26])).
% 6.60/2.37  tff(c_9264, plain, (r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5571, c_9255])).
% 6.60/2.37  tff(c_9266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4235, c_9264])).
% 6.60/2.37  tff(c_9268, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_4753])).
% 6.60/2.37  tff(c_9267, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_4753])).
% 6.60/2.37  tff(c_9352, plain, (![A_741]: (~v1_xboole_0(A_741) | A_741='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_9267, c_58])).
% 6.60/2.37  tff(c_9367, plain, ('#skF_7'='#skF_4'), inference(resolution, [status(thm)], [c_9268, c_9352])).
% 6.60/2.37  tff(c_9376, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9367, c_9267])).
% 6.60/2.37  tff(c_4268, plain, (![B_498, C_497]: (r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_498, C_497))), C_497) | k2_zfmisc_1(B_498, C_497)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_4258])).
% 6.60/2.37  tff(c_9672, plain, (![B_763, C_764]: (r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_763, C_764))), C_764) | k2_zfmisc_1(B_763, C_764)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9376, c_4268])).
% 6.60/2.37  tff(c_9282, plain, (![A_13]: (~r2_hidden(A_13, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_9267, c_4354])).
% 6.60/2.37  tff(c_9373, plain, (![A_13]: (~r2_hidden(A_13, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9367, c_9282])).
% 6.60/2.37  tff(c_9701, plain, (![B_763]: (k2_zfmisc_1(B_763, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_9672, c_9373])).
% 6.60/2.37  tff(c_4294, plain, (![A_505, B_506]: (~v1_xboole_0(A_505) | v1_xboole_0(k2_zfmisc_1(A_505, B_506)))), inference(resolution, [status(thm)], [c_4, c_4280])).
% 6.60/2.37  tff(c_4410, plain, (![A_527, B_528, C_529]: (~v1_xboole_0(k2_zfmisc_1(A_527, B_528)) | v1_xboole_0(k3_zfmisc_1(A_527, B_528, C_529)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4294])).
% 6.60/2.37  tff(c_4426, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_4410, c_73])).
% 6.60/2.37  tff(c_9377, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9367, c_4426])).
% 6.60/2.37  tff(c_9710, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9701, c_9377])).
% 6.60/2.37  tff(c_9713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9268, c_9710])).
% 6.60/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.60/2.37  
% 6.60/2.37  Inference rules
% 6.60/2.37  ----------------------
% 6.60/2.37  #Ref     : 0
% 6.60/2.37  #Sup     : 2301
% 6.60/2.37  #Fact    : 0
% 6.60/2.37  #Define  : 0
% 6.60/2.37  #Split   : 27
% 6.60/2.37  #Chain   : 0
% 6.60/2.37  #Close   : 0
% 6.60/2.37  
% 6.60/2.37  Ordering : KBO
% 6.60/2.37  
% 6.60/2.37  Simplification rules
% 6.60/2.37  ----------------------
% 6.60/2.37  #Subsume      : 568
% 6.60/2.37  #Demod        : 1505
% 6.60/2.37  #Tautology    : 1075
% 6.60/2.37  #SimpNegUnit  : 81
% 6.60/2.37  #BackRed      : 346
% 6.60/2.37  
% 6.60/2.37  #Partial instantiations: 0
% 6.60/2.37  #Strategies tried      : 1
% 6.60/2.37  
% 6.60/2.37  Timing (in seconds)
% 6.60/2.37  ----------------------
% 6.60/2.37  Preprocessing        : 0.34
% 6.60/2.37  Parsing              : 0.18
% 6.60/2.37  CNF conversion       : 0.03
% 6.60/2.37  Main loop            : 1.23
% 6.60/2.37  Inferencing          : 0.41
% 6.60/2.37  Reduction            : 0.41
% 6.60/2.37  Demodulation         : 0.28
% 6.60/2.37  BG Simplification    : 0.05
% 6.60/2.37  Subsumption          : 0.25
% 6.60/2.37  Abstraction          : 0.06
% 6.60/2.37  MUC search           : 0.00
% 6.60/2.37  Cooper               : 0.00
% 6.60/2.37  Total                : 1.64
% 6.60/2.37  Index Insertion      : 0.00
% 6.60/2.37  Index Deletion       : 0.00
% 6.60/2.37  Index Matching       : 0.00
% 6.60/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
