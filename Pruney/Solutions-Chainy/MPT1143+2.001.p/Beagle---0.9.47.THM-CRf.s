%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:22 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 375 expanded)
%              Number of leaves         :   41 ( 135 expanded)
%              Depth                    :   17
%              Number of atoms          :  179 ( 949 expanded)
%              Number of equality atoms :   16 ( 106 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v6_orders_2 > r7_relat_2 > r2_hidden > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r7_relat_2,type,(
    r7_relat_2: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
              & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r7_relat_2(A,B)
        <=> ! [C,D] :
              ~ ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & ~ r2_hidden(k4_tarski(C,D),A)
                & ~ r2_hidden(k4_tarski(D,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_54,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42,plain,(
    ! [A_43] :
      ( l1_struct_0(A_43)
      | ~ l1_orders_2(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_425,plain,(
    ! [A_133,B_134] :
      ( k6_domain_1(A_133,B_134) = k1_tarski(B_134)
      | ~ m1_subset_1(B_134,A_133)
      | v1_xboole_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_433,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_425])).

tff(c_434,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_20,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(u1_struct_0(A_13))
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_437,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_434,c_20])).

tff(c_440,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_437])).

tff(c_443,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_440])).

tff(c_447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_443])).

tff(c_449,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tarski(A_6),k1_zfmisc_1(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_448,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_56,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_204,plain,(
    ! [A_93,B_94] :
      ( r1_orders_2(A_93,B_94,B_94)
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_206,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_204])).

tff(c_209,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_206])).

tff(c_210,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_209])).

tff(c_372,plain,(
    ! [B_118,C_119,A_120] :
      ( r2_hidden(k4_tarski(B_118,C_119),u1_orders_2(A_120))
      | ~ r1_orders_2(A_120,B_118,C_119)
      | ~ m1_subset_1(C_119,u1_struct_0(A_120))
      | ~ m1_subset_1(B_118,u1_struct_0(A_120))
      | ~ l1_orders_2(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_111,plain,(
    ! [A_72,B_73] :
      ( k6_domain_1(A_72,B_73) = k1_tarski(B_73)
      | ~ m1_subset_1(B_73,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_119,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_111])).

tff(c_120,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_123,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_120,c_20])).

tff(c_126,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_123])).

tff(c_129,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_129])).

tff(c_134,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_50,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_69,plain,(
    ~ v6_orders_2(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_136,plain,(
    ~ v6_orders_2(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_69])).

tff(c_135,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_142,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1(k6_domain_1(A_76,B_77),k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_77,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_152,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_142])).

tff(c_156,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_152])).

tff(c_157,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_156])).

tff(c_211,plain,(
    ! [B_95,A_96] :
      ( v6_orders_2(B_95,A_96)
      | ~ r7_relat_2(u1_orders_2(A_96),B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_orders_2(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_214,plain,
    ( v6_orders_2(k1_tarski('#skF_6'),'#skF_5')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),k1_tarski('#skF_6'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_157,c_211])).

tff(c_225,plain,
    ( v6_orders_2(k1_tarski('#skF_6'),'#skF_5')
    | ~ r7_relat_2(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_214])).

tff(c_226,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_225])).

tff(c_162,plain,(
    ! [A_78] :
      ( m1_subset_1(u1_orders_2(A_78),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78),u1_struct_0(A_78))))
      | ~ l1_orders_2(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_18,plain,(
    ! [C_12,A_10,B_11] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_170,plain,(
    ! [A_78] :
      ( v1_relat_1(u1_orders_2(A_78))
      | ~ l1_orders_2(A_78) ) ),
    inference(resolution,[status(thm)],[c_162,c_18])).

tff(c_89,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_4'(A_68,B_69),B_69)
      | r7_relat_2(A_68,B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [A_68,A_1] :
      ( '#skF_4'(A_68,k1_tarski(A_1)) = A_1
      | r7_relat_2(A_68,k1_tarski(A_1))
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_235,plain,
    ( '#skF_4'(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_99,c_226])).

tff(c_237,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_240,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_170,c_237])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_240])).

tff(c_246,plain,(
    v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_245,plain,(
    '#skF_4'(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_100,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_3'(A_70,B_71),B_71)
      | r7_relat_2(A_70,B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_110,plain,(
    ! [A_70,A_1] :
      ( '#skF_3'(A_70,k1_tarski(A_1)) = A_1
      | r7_relat_2(A_70,k1_tarski(A_1))
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_236,plain,
    ( '#skF_3'(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_110,c_226])).

tff(c_270,plain,(
    '#skF_3'(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_236])).

tff(c_30,plain,(
    ! [A_17,B_27] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_17,B_27),'#skF_4'(A_17,B_27)),A_17)
      | r7_relat_2(A_17,B_27)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_274,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_4'(u1_orders_2('#skF_5'),k1_tarski('#skF_6'))),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k1_tarski('#skF_6'))
    | ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_30])).

tff(c_281,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_6'),u1_orders_2('#skF_5'))
    | r7_relat_2(u1_orders_2('#skF_5'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_245,c_274])).

tff(c_282,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_6'),u1_orders_2('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_281])).

tff(c_382,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_372,c_282])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_210,c_382])).

tff(c_393,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_450,plain,(
    ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_393])).

tff(c_459,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_14,c_450])).

tff(c_473,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_459])).

tff(c_476,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_473])).

tff(c_478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:01:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.38  
% 2.68/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.38  %$ r1_orders_2 > v6_orders_2 > r7_relat_2 > r2_hidden > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.68/1.38  
% 2.68/1.38  %Foreground sorts:
% 2.68/1.38  
% 2.68/1.38  
% 2.68/1.38  %Background operators:
% 2.68/1.38  
% 2.68/1.38  
% 2.68/1.38  %Foreground operators:
% 2.68/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.38  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.68/1.38  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.68/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.68/1.38  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.68/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.68/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.68/1.38  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.38  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.68/1.38  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.68/1.38  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.68/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.68/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.38  
% 2.68/1.40  tff(f_141, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 2.68/1.40  tff(f_103, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.68/1.40  tff(f_114, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.68/1.40  tff(f_54, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.68/1.40  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.68/1.40  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.68/1.40  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 2.68/1.40  tff(f_92, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 2.68/1.40  tff(f_99, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.68/1.40  tff(f_63, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_orders_2)).
% 2.68/1.40  tff(f_107, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.68/1.40  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.68/1.40  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (r7_relat_2(A, B) <=> (![C, D]: ~(((r2_hidden(C, B) & r2_hidden(D, B)) & ~r2_hidden(k4_tarski(C, D), A)) & ~r2_hidden(k4_tarski(D, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_2)).
% 2.68/1.40  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.68/1.40  tff(c_54, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.68/1.40  tff(c_42, plain, (![A_43]: (l1_struct_0(A_43) | ~l1_orders_2(A_43))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.68/1.40  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.68/1.40  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.68/1.40  tff(c_425, plain, (![A_133, B_134]: (k6_domain_1(A_133, B_134)=k1_tarski(B_134) | ~m1_subset_1(B_134, A_133) | v1_xboole_0(A_133))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.68/1.40  tff(c_433, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_425])).
% 2.68/1.40  tff(c_434, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_433])).
% 2.68/1.40  tff(c_20, plain, (![A_13]: (~v1_xboole_0(u1_struct_0(A_13)) | ~l1_struct_0(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.68/1.40  tff(c_437, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_434, c_20])).
% 2.68/1.40  tff(c_440, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_437])).
% 2.68/1.40  tff(c_443, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_42, c_440])).
% 2.68/1.40  tff(c_447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_443])).
% 2.68/1.40  tff(c_449, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_433])).
% 2.68/1.40  tff(c_16, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.68/1.40  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(k1_tarski(A_6), k1_zfmisc_1(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.68/1.40  tff(c_448, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_433])).
% 2.68/1.40  tff(c_56, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.68/1.40  tff(c_204, plain, (![A_93, B_94]: (r1_orders_2(A_93, B_94, B_94) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~l1_orders_2(A_93) | ~v3_orders_2(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.68/1.40  tff(c_206, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_6') | ~l1_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_204])).
% 2.68/1.40  tff(c_209, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_206])).
% 2.68/1.40  tff(c_210, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_209])).
% 2.68/1.40  tff(c_372, plain, (![B_118, C_119, A_120]: (r2_hidden(k4_tarski(B_118, C_119), u1_orders_2(A_120)) | ~r1_orders_2(A_120, B_118, C_119) | ~m1_subset_1(C_119, u1_struct_0(A_120)) | ~m1_subset_1(B_118, u1_struct_0(A_120)) | ~l1_orders_2(A_120))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.68/1.40  tff(c_111, plain, (![A_72, B_73]: (k6_domain_1(A_72, B_73)=k1_tarski(B_73) | ~m1_subset_1(B_73, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.68/1.40  tff(c_119, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_111])).
% 2.68/1.40  tff(c_120, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_119])).
% 2.68/1.40  tff(c_123, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_120, c_20])).
% 2.68/1.40  tff(c_126, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_123])).
% 2.68/1.40  tff(c_129, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_42, c_126])).
% 2.68/1.40  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_129])).
% 2.68/1.40  tff(c_134, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_119])).
% 2.68/1.40  tff(c_50, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v6_orders_2(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.68/1.40  tff(c_69, plain, (~v6_orders_2(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 2.68/1.40  tff(c_136, plain, (~v6_orders_2(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_69])).
% 2.68/1.40  tff(c_135, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_119])).
% 2.68/1.40  tff(c_142, plain, (![A_76, B_77]: (m1_subset_1(k6_domain_1(A_76, B_77), k1_zfmisc_1(A_76)) | ~m1_subset_1(B_77, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.68/1.40  tff(c_152, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_142])).
% 2.68/1.40  tff(c_156, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_152])).
% 2.68/1.40  tff(c_157, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_135, c_156])).
% 2.68/1.40  tff(c_211, plain, (![B_95, A_96]: (v6_orders_2(B_95, A_96) | ~r7_relat_2(u1_orders_2(A_96), B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_orders_2(A_96))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.68/1.40  tff(c_214, plain, (v6_orders_2(k1_tarski('#skF_6'), '#skF_5') | ~r7_relat_2(u1_orders_2('#skF_5'), k1_tarski('#skF_6')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_157, c_211])).
% 2.68/1.40  tff(c_225, plain, (v6_orders_2(k1_tarski('#skF_6'), '#skF_5') | ~r7_relat_2(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_214])).
% 2.68/1.40  tff(c_226, plain, (~r7_relat_2(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_136, c_225])).
% 2.68/1.40  tff(c_162, plain, (![A_78]: (m1_subset_1(u1_orders_2(A_78), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78), u1_struct_0(A_78)))) | ~l1_orders_2(A_78))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.68/1.40  tff(c_18, plain, (![C_12, A_10, B_11]: (v1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.40  tff(c_170, plain, (![A_78]: (v1_relat_1(u1_orders_2(A_78)) | ~l1_orders_2(A_78))), inference(resolution, [status(thm)], [c_162, c_18])).
% 2.68/1.40  tff(c_89, plain, (![A_68, B_69]: (r2_hidden('#skF_4'(A_68, B_69), B_69) | r7_relat_2(A_68, B_69) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.68/1.40  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.40  tff(c_99, plain, (![A_68, A_1]: ('#skF_4'(A_68, k1_tarski(A_1))=A_1 | r7_relat_2(A_68, k1_tarski(A_1)) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_89, c_2])).
% 2.68/1.40  tff(c_235, plain, ('#skF_4'(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_99, c_226])).
% 2.68/1.40  tff(c_237, plain, (~v1_relat_1(u1_orders_2('#skF_5'))), inference(splitLeft, [status(thm)], [c_235])).
% 2.68/1.40  tff(c_240, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_170, c_237])).
% 2.68/1.40  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_240])).
% 2.68/1.40  tff(c_246, plain, (v1_relat_1(u1_orders_2('#skF_5'))), inference(splitRight, [status(thm)], [c_235])).
% 2.68/1.40  tff(c_245, plain, ('#skF_4'(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_235])).
% 2.68/1.40  tff(c_100, plain, (![A_70, B_71]: (r2_hidden('#skF_3'(A_70, B_71), B_71) | r7_relat_2(A_70, B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.68/1.40  tff(c_110, plain, (![A_70, A_1]: ('#skF_3'(A_70, k1_tarski(A_1))=A_1 | r7_relat_2(A_70, k1_tarski(A_1)) | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_100, c_2])).
% 2.68/1.40  tff(c_236, plain, ('#skF_3'(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_110, c_226])).
% 2.68/1.40  tff(c_270, plain, ('#skF_3'(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_236])).
% 2.68/1.40  tff(c_30, plain, (![A_17, B_27]: (~r2_hidden(k4_tarski('#skF_3'(A_17, B_27), '#skF_4'(A_17, B_27)), A_17) | r7_relat_2(A_17, B_27) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.68/1.40  tff(c_274, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_4'(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))), u1_orders_2('#skF_5')) | r7_relat_2(u1_orders_2('#skF_5'), k1_tarski('#skF_6')) | ~v1_relat_1(u1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_30])).
% 2.68/1.40  tff(c_281, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_6'), u1_orders_2('#skF_5')) | r7_relat_2(u1_orders_2('#skF_5'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_245, c_274])).
% 2.68/1.40  tff(c_282, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_6'), u1_orders_2('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_226, c_281])).
% 2.68/1.40  tff(c_382, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_372, c_282])).
% 2.68/1.40  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_210, c_382])).
% 2.68/1.40  tff(c_393, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_50])).
% 2.68/1.40  tff(c_450, plain, (~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_393])).
% 2.68/1.40  tff(c_459, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_450])).
% 2.68/1.40  tff(c_473, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_459])).
% 2.68/1.40  tff(c_476, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_473])).
% 2.68/1.40  tff(c_478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_449, c_476])).
% 2.68/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.40  
% 2.68/1.40  Inference rules
% 2.68/1.40  ----------------------
% 2.68/1.40  #Ref     : 0
% 2.68/1.40  #Sup     : 76
% 2.68/1.40  #Fact    : 0
% 2.68/1.40  #Define  : 0
% 2.68/1.40  #Split   : 6
% 2.68/1.40  #Chain   : 0
% 2.68/1.40  #Close   : 0
% 2.68/1.40  
% 2.68/1.40  Ordering : KBO
% 2.68/1.40  
% 2.68/1.40  Simplification rules
% 2.68/1.40  ----------------------
% 2.68/1.40  #Subsume      : 4
% 2.68/1.40  #Demod        : 30
% 2.68/1.40  #Tautology    : 19
% 2.68/1.40  #SimpNegUnit  : 13
% 2.68/1.40  #BackRed      : 3
% 2.68/1.40  
% 2.68/1.40  #Partial instantiations: 0
% 2.68/1.40  #Strategies tried      : 1
% 2.68/1.40  
% 2.68/1.40  Timing (in seconds)
% 2.68/1.40  ----------------------
% 2.68/1.40  Preprocessing        : 0.35
% 2.68/1.40  Parsing              : 0.19
% 2.68/1.40  CNF conversion       : 0.03
% 2.68/1.40  Main loop            : 0.28
% 2.68/1.40  Inferencing          : 0.10
% 2.68/1.40  Reduction            : 0.08
% 2.68/1.40  Demodulation         : 0.05
% 2.68/1.40  BG Simplification    : 0.02
% 2.68/1.40  Subsumption          : 0.05
% 2.68/1.40  Abstraction          : 0.02
% 2.68/1.40  MUC search           : 0.00
% 2.68/1.40  Cooper               : 0.00
% 2.68/1.40  Total                : 0.67
% 2.68/1.40  Index Insertion      : 0.00
% 2.68/1.40  Index Deletion       : 0.00
% 2.68/1.40  Index Matching       : 0.00
% 2.68/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
