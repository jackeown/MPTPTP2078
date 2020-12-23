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
% DateTime   : Thu Dec  3 10:17:40 EST 2020

% Result     : Theorem 20.91s
% Output     : CNFRefutation 20.91s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 230 expanded)
%              Number of leaves         :   35 (  98 expanded)
%              Depth                    :   23
%              Number of atoms          :  293 ( 853 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k6_funct_2,type,(
    k6_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_funct_2,type,(
    k7_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                   => r1_tarski(k5_setfam_1(A,D),k5_setfam_1(A,k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_funct_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(A))
                     => ( m1_setfam_1(D,E)
                       => m1_setfam_1(k6_funct_2(A,B,C,k7_funct_2(A,B,C,D)),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_funct_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(A))) )
     => m1_subset_1(k7_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(B))) )
     => m1_subset_1(k6_funct_2(A,B,C,D),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_funct_2)).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_56,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,B_74)
      | ~ m1_subset_1(A_73,k1_zfmisc_1(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_64,plain,(
    r1_tarski('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_tarski(k3_tarski(A_7),B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_127,plain,(
    ! [C_94,A_95,B_96] :
      ( r2_hidden(C_94,A_95)
      | ~ r2_hidden(C_94,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_970,plain,(
    ! [A_200,B_201,A_202] :
      ( r2_hidden('#skF_3'(A_200,B_201),A_202)
      | ~ m1_subset_1(A_200,k1_zfmisc_1(A_202))
      | r1_tarski(k3_tarski(A_200),B_201) ) ),
    inference(resolution,[status(thm)],[c_18,c_127])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2783,plain,(
    ! [A_331,B_332,A_333] :
      ( r1_tarski('#skF_3'(A_331,B_332),A_333)
      | ~ m1_subset_1(A_331,k1_zfmisc_1(k1_zfmisc_1(A_333)))
      | r1_tarski(k3_tarski(A_331),B_332) ) ),
    inference(resolution,[status(thm)],[c_970,c_2])).

tff(c_2817,plain,(
    ! [A_335,B_336,A_337] :
      ( r1_tarski('#skF_3'(A_335,B_336),A_337)
      | r1_tarski(k3_tarski(A_335),B_336)
      | ~ r1_tarski(A_335,k1_zfmisc_1(A_337)) ) ),
    inference(resolution,[status(thm)],[c_30,c_2783])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( ~ r1_tarski('#skF_3'(A_7,B_8),B_8)
      | r1_tarski(k3_tarski(A_7),B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2867,plain,(
    ! [A_335,A_337] :
      ( r1_tarski(k3_tarski(A_335),A_337)
      | ~ r1_tarski(A_335,k1_zfmisc_1(A_337)) ) ),
    inference(resolution,[status(thm)],[c_2817,c_16])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_63,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_56])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_14,plain,(
    ! [A_6] : r1_tarski(A_6,k1_zfmisc_1(k3_tarski(A_6))) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_93,plain,(
    ! [A_89,B_90] :
      ( k5_setfam_1(A_89,B_90) = k3_tarski(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(A_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_108,plain,(
    ! [A_91,A_92] :
      ( k5_setfam_1(A_91,A_92) = k3_tarski(A_92)
      | ~ r1_tarski(A_92,k1_zfmisc_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_30,c_93])).

tff(c_117,plain,(
    ! [A_6] : k5_setfam_1(k3_tarski(A_6),A_6) = k3_tarski(A_6) ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_223,plain,(
    ! [B_112,A_113] :
      ( m1_setfam_1(B_112,A_113)
      | k5_setfam_1(A_113,B_112) != A_113
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(A_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_443,plain,(
    ! [A_138,A_139] :
      ( m1_setfam_1(A_138,A_139)
      | k5_setfam_1(A_139,A_138) != A_139
      | ~ r1_tarski(A_138,k1_zfmisc_1(A_139)) ) ),
    inference(resolution,[status(thm)],[c_30,c_223])).

tff(c_463,plain,(
    ! [A_6] :
      ( m1_setfam_1(A_6,k3_tarski(A_6))
      | k5_setfam_1(k3_tarski(A_6),A_6) != k3_tarski(A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_443])).

tff(c_472,plain,(
    ! [A_6] : m1_setfam_1(A_6,k3_tarski(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_463])).

tff(c_901,plain,(
    ! [B_191,E_193,C_194,A_192,D_190] :
      ( m1_setfam_1(k6_funct_2(A_192,B_191,C_194,k7_funct_2(A_192,B_191,C_194,D_190)),E_193)
      | ~ m1_setfam_1(D_190,E_193)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(A_192))
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k1_zfmisc_1(A_192)))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_191)))
      | ~ v1_funct_2(C_194,A_192,B_191)
      | ~ v1_funct_1(C_194)
      | v1_xboole_0(B_191)
      | v1_xboole_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3730,plain,(
    ! [C_406,B_408,A_409,E_410,A_407] :
      ( m1_setfam_1(k6_funct_2(A_409,B_408,C_406,k7_funct_2(A_409,B_408,C_406,A_407)),E_410)
      | ~ m1_setfam_1(A_407,E_410)
      | ~ m1_subset_1(E_410,k1_zfmisc_1(A_409))
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(A_409,B_408)))
      | ~ v1_funct_2(C_406,A_409,B_408)
      | ~ v1_funct_1(C_406)
      | v1_xboole_0(B_408)
      | v1_xboole_0(A_409)
      | ~ r1_tarski(A_407,k1_zfmisc_1(A_409)) ) ),
    inference(resolution,[status(thm)],[c_30,c_901])).

tff(c_3736,plain,(
    ! [B_408,A_409,E_410,A_407,A_18] :
      ( m1_setfam_1(k6_funct_2(A_409,B_408,A_18,k7_funct_2(A_409,B_408,A_18,A_407)),E_410)
      | ~ m1_setfam_1(A_407,E_410)
      | ~ m1_subset_1(E_410,k1_zfmisc_1(A_409))
      | ~ v1_funct_2(A_18,A_409,B_408)
      | ~ v1_funct_1(A_18)
      | v1_xboole_0(B_408)
      | v1_xboole_0(A_409)
      | ~ r1_tarski(A_407,k1_zfmisc_1(A_409))
      | ~ r1_tarski(A_18,k2_zfmisc_1(A_409,B_408)) ) ),
    inference(resolution,[status(thm)],[c_30,c_3730])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,k3_tarski(B_15))
      | ~ m1_setfam_1(B_15,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( m1_subset_1(k7_funct_2(A_26,B_27,C_28,D_29),k1_zfmisc_1(k1_zfmisc_1(B_27)))
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k1_zfmisc_1(A_26)))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_2(C_28,A_26,B_27)
      | ~ v1_funct_1(C_28)
      | v1_xboole_0(B_27)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_910,plain,(
    ! [B_191,C_194,E_193] :
      ( m1_setfam_1(k6_funct_2('#skF_4',B_191,C_194,k7_funct_2('#skF_4',B_191,C_194,'#skF_7')),E_193)
      | ~ m1_setfam_1('#skF_7',E_193)
      | ~ m1_subset_1(E_193,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_191)))
      | ~ v1_funct_2(C_194,'#skF_4',B_191)
      | ~ v1_funct_1(C_194)
      | v1_xboole_0(B_191)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_901])).

tff(c_921,plain,(
    ! [B_196,C_197,E_198] :
      ( m1_setfam_1(k6_funct_2('#skF_4',B_196,C_197,k7_funct_2('#skF_4',B_196,C_197,'#skF_7')),E_198)
      | ~ m1_setfam_1('#skF_7',E_198)
      | ~ m1_subset_1(E_198,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_196)))
      | ~ v1_funct_2(C_197,'#skF_4',B_196)
      | ~ v1_funct_1(C_197)
      | v1_xboole_0(B_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_910])).

tff(c_926,plain,(
    ! [E_198] :
      ( m1_setfam_1(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')),E_198)
      | ~ m1_setfam_1('#skF_7',E_198)
      | ~ m1_subset_1(E_198,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_921])).

tff(c_930,plain,(
    ! [E_198] :
      ( m1_setfam_1(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')),E_198)
      | ~ m1_setfam_1('#skF_7',E_198)
      | ~ m1_subset_1(E_198,k1_zfmisc_1('#skF_4'))
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_926])).

tff(c_931,plain,(
    ! [E_198] :
      ( m1_setfam_1(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')),E_198)
      | ~ m1_setfam_1('#skF_7',E_198)
      | ~ m1_subset_1(E_198,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_930])).

tff(c_36,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( m1_subset_1(k6_funct_2(A_22,B_23,C_24,D_25),k1_zfmisc_1(k1_zfmisc_1(A_22)))
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k1_zfmisc_1(B_23)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24)
      | v1_xboole_0(B_23)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3888,plain,(
    ! [C_421,A_419,C_420,E_425,B_424,D_423,B_422] :
      ( m1_setfam_1(k6_funct_2(A_419,B_422,C_420,k7_funct_2(A_419,B_422,C_420,k6_funct_2(A_419,B_424,C_421,D_423))),E_425)
      | ~ m1_setfam_1(k6_funct_2(A_419,B_424,C_421,D_423),E_425)
      | ~ m1_subset_1(E_425,k1_zfmisc_1(A_419))
      | ~ m1_subset_1(C_420,k1_zfmisc_1(k2_zfmisc_1(A_419,B_422)))
      | ~ v1_funct_2(C_420,A_419,B_422)
      | ~ v1_funct_1(C_420)
      | v1_xboole_0(B_422)
      | ~ m1_subset_1(D_423,k1_zfmisc_1(k1_zfmisc_1(B_424)))
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(A_419,B_424)))
      | ~ v1_funct_2(C_421,A_419,B_424)
      | ~ v1_funct_1(C_421)
      | v1_xboole_0(B_424)
      | v1_xboole_0(A_419) ) ),
    inference(resolution,[status(thm)],[c_36,c_901])).

tff(c_88,plain,(
    ! [A_87,B_88] :
      ( ~ r1_tarski('#skF_3'(A_87,B_88),B_88)
      | r1_tarski(k3_tarski(A_87),B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    ! [A_87,B_15] :
      ( r1_tarski(k3_tarski(A_87),k3_tarski(B_15))
      | ~ m1_setfam_1(B_15,'#skF_3'(A_87,k3_tarski(B_15))) ) ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_34766,plain,(
    ! [A_1713,C_1709,A_1712,B_1715,B_1714,D_1710,C_1711] :
      ( r1_tarski(k3_tarski(A_1712),k3_tarski(k6_funct_2(A_1713,B_1715,C_1709,k7_funct_2(A_1713,B_1715,C_1709,k6_funct_2(A_1713,B_1714,C_1711,D_1710)))))
      | ~ m1_setfam_1(k6_funct_2(A_1713,B_1714,C_1711,D_1710),'#skF_3'(A_1712,k3_tarski(k6_funct_2(A_1713,B_1715,C_1709,k7_funct_2(A_1713,B_1715,C_1709,k6_funct_2(A_1713,B_1714,C_1711,D_1710))))))
      | ~ m1_subset_1('#skF_3'(A_1712,k3_tarski(k6_funct_2(A_1713,B_1715,C_1709,k7_funct_2(A_1713,B_1715,C_1709,k6_funct_2(A_1713,B_1714,C_1711,D_1710))))),k1_zfmisc_1(A_1713))
      | ~ m1_subset_1(C_1709,k1_zfmisc_1(k2_zfmisc_1(A_1713,B_1715)))
      | ~ v1_funct_2(C_1709,A_1713,B_1715)
      | ~ v1_funct_1(C_1709)
      | v1_xboole_0(B_1715)
      | ~ m1_subset_1(D_1710,k1_zfmisc_1(k1_zfmisc_1(B_1714)))
      | ~ m1_subset_1(C_1711,k1_zfmisc_1(k2_zfmisc_1(A_1713,B_1714)))
      | ~ v1_funct_2(C_1711,A_1713,B_1714)
      | ~ v1_funct_1(C_1711)
      | v1_xboole_0(B_1714)
      | v1_xboole_0(A_1713) ) ),
    inference(resolution,[status(thm)],[c_3888,c_92])).

tff(c_34814,plain,(
    ! [A_1712,B_1715,C_1709] :
      ( r1_tarski(k3_tarski(A_1712),k3_tarski(k6_funct_2('#skF_4',B_1715,C_1709,k7_funct_2('#skF_4',B_1715,C_1709,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))))))
      | ~ m1_subset_1(C_1709,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1715)))
      | ~ v1_funct_2(C_1709,'#skF_4',B_1715)
      | ~ v1_funct_1(C_1709)
      | v1_xboole_0(B_1715)
      | ~ m1_subset_1(k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_setfam_1('#skF_7','#skF_3'(A_1712,k3_tarski(k6_funct_2('#skF_4',B_1715,C_1709,k7_funct_2('#skF_4',B_1715,C_1709,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))))
      | ~ m1_subset_1('#skF_3'(A_1712,k3_tarski(k6_funct_2('#skF_4',B_1715,C_1709,k7_funct_2('#skF_4',B_1715,C_1709,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))),k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_931,c_34766])).

tff(c_34837,plain,(
    ! [A_1712,B_1715,C_1709] :
      ( r1_tarski(k3_tarski(A_1712),k3_tarski(k6_funct_2('#skF_4',B_1715,C_1709,k7_funct_2('#skF_4',B_1715,C_1709,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))))))
      | ~ m1_subset_1(C_1709,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1715)))
      | ~ v1_funct_2(C_1709,'#skF_4',B_1715)
      | ~ v1_funct_1(C_1709)
      | v1_xboole_0(B_1715)
      | ~ m1_subset_1(k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_5')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_setfam_1('#skF_7','#skF_3'(A_1712,k3_tarski(k6_funct_2('#skF_4',B_1715,C_1709,k7_funct_2('#skF_4',B_1715,C_1709,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))))
      | ~ m1_subset_1('#skF_3'(A_1712,k3_tarski(k6_funct_2('#skF_4',B_1715,C_1709,k7_funct_2('#skF_4',B_1715,C_1709,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))),k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_34814])).

tff(c_34838,plain,(
    ! [A_1712,B_1715,C_1709] :
      ( r1_tarski(k3_tarski(A_1712),k3_tarski(k6_funct_2('#skF_4',B_1715,C_1709,k7_funct_2('#skF_4',B_1715,C_1709,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))))))
      | ~ m1_subset_1(C_1709,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1715)))
      | ~ v1_funct_2(C_1709,'#skF_4',B_1715)
      | ~ v1_funct_1(C_1709)
      | v1_xboole_0(B_1715)
      | ~ m1_subset_1(k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_5')))
      | ~ m1_setfam_1('#skF_7','#skF_3'(A_1712,k3_tarski(k6_funct_2('#skF_4',B_1715,C_1709,k7_funct_2('#skF_4',B_1715,C_1709,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))))
      | ~ m1_subset_1('#skF_3'(A_1712,k3_tarski(k6_funct_2('#skF_4',B_1715,C_1709,k7_funct_2('#skF_4',B_1715,C_1709,k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))))),k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_34837])).

tff(c_34894,plain,(
    ~ m1_subset_1(k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_34838])).

tff(c_34897,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_34894])).

tff(c_34903,plain,
    ( v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_34897])).

tff(c_34905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_34903])).

tff(c_34907,plain,(
    m1_subset_1(k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_34838])).

tff(c_825,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( m1_subset_1(k6_funct_2(A_176,B_177,C_178,D_179),k1_zfmisc_1(k1_zfmisc_1(A_176)))
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k1_zfmisc_1(B_177)))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_2(C_178,A_176,B_177)
      | ~ v1_funct_1(C_178)
      | v1_xboole_0(B_177)
      | v1_xboole_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( k5_setfam_1(A_16,B_17) = k3_tarski(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_840,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( k5_setfam_1(A_176,k6_funct_2(A_176,B_177,C_178,D_179)) = k3_tarski(k6_funct_2(A_176,B_177,C_178,D_179))
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k1_zfmisc_1(B_177)))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_2(C_178,A_176,B_177)
      | ~ v1_funct_1(C_178)
      | v1_xboole_0(B_177)
      | v1_xboole_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_825,c_26])).

tff(c_34943,plain,(
    ! [A_176,C_178] :
      ( k5_setfam_1(A_176,k6_funct_2(A_176,'#skF_5',C_178,k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) = k3_tarski(k6_funct_2(A_176,'#skF_5',C_178,k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,'#skF_5')))
      | ~ v1_funct_2(C_178,A_176,'#skF_5')
      | ~ v1_funct_1(C_178)
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_34907,c_840])).

tff(c_35887,plain,(
    ! [A_1746,C_1747] :
      ( k5_setfam_1(A_1746,k6_funct_2(A_1746,'#skF_5',C_1747,k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) = k3_tarski(k6_funct_2(A_1746,'#skF_5',C_1747,k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))
      | ~ m1_subset_1(C_1747,k1_zfmisc_1(k2_zfmisc_1(A_1746,'#skF_5')))
      | ~ v1_funct_2(C_1747,A_1746,'#skF_5')
      | ~ v1_funct_1(C_1747)
      | v1_xboole_0(A_1746) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_34943])).

tff(c_35892,plain,
    ( k5_setfam_1('#skF_4',k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) = k3_tarski(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_35887])).

tff(c_35896,plain,
    ( k5_setfam_1('#skF_4',k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) = k3_tarski(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_35892])).

tff(c_35897,plain,(
    k5_setfam_1('#skF_4',k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) = k3_tarski(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_35896])).

tff(c_102,plain,(
    k5_setfam_1('#skF_4','#skF_7') = k3_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_93])).

tff(c_42,plain,(
    ~ r1_tarski(k5_setfam_1('#skF_4','#skF_7'),k5_setfam_1('#skF_4',k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_103,plain,(
    ~ r1_tarski(k3_tarski('#skF_7'),k5_setfam_1('#skF_4',k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_42])).

tff(c_36732,plain,(
    ~ r1_tarski(k3_tarski('#skF_7'),k3_tarski(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35897,c_103])).

tff(c_36752,plain,(
    ~ m1_setfam_1(k6_funct_2('#skF_4','#skF_5','#skF_6',k7_funct_2('#skF_4','#skF_5','#skF_6','#skF_7')),k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_22,c_36732])).

tff(c_36755,plain,
    ( ~ m1_setfam_1('#skF_7',k3_tarski('#skF_7'))
    | ~ m1_subset_1(k3_tarski('#skF_7'),k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | ~ r1_tarski('#skF_7',k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_3736,c_36752])).

tff(c_36767,plain,
    ( ~ m1_subset_1(k3_tarski('#skF_7'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_50,c_48,c_472,c_36755])).

tff(c_36768,plain,(
    ~ m1_subset_1(k3_tarski('#skF_7'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_36767])).

tff(c_36782,plain,(
    ~ r1_tarski(k3_tarski('#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_36768])).

tff(c_36794,plain,(
    ~ r1_tarski('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2867,c_36782])).

tff(c_36807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_36794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.91/11.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.91/11.37  
% 20.91/11.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.91/11.37  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > v1_funct_1 > k7_funct_2 > k6_funct_2 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 20.91/11.37  
% 20.91/11.37  %Foreground sorts:
% 20.91/11.37  
% 20.91/11.37  
% 20.91/11.37  %Background operators:
% 20.91/11.37  
% 20.91/11.37  
% 20.91/11.37  %Foreground operators:
% 20.91/11.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.91/11.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.91/11.37  tff(k6_funct_2, type, k6_funct_2: ($i * $i * $i * $i) > $i).
% 20.91/11.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.91/11.37  tff('#skF_7', type, '#skF_7': $i).
% 20.91/11.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.91/11.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.91/11.37  tff('#skF_5', type, '#skF_5': $i).
% 20.91/11.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 20.91/11.37  tff('#skF_6', type, '#skF_6': $i).
% 20.91/11.37  tff(k7_funct_2, type, k7_funct_2: ($i * $i * $i * $i) > $i).
% 20.91/11.37  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 20.91/11.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.91/11.37  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 20.91/11.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.91/11.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.91/11.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.91/11.37  tff('#skF_4', type, '#skF_4': $i).
% 20.91/11.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.91/11.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 20.91/11.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.91/11.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 20.91/11.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.91/11.37  
% 20.91/11.39  tff(f_142, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => r1_tarski(k5_setfam_1(A, D), k5_setfam_1(A, k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_funct_2)).
% 20.91/11.39  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 20.91/11.39  tff(f_41, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 20.91/11.39  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 20.91/11.39  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 20.91/11.39  tff(f_34, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 20.91/11.39  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 20.91/11.39  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 20.91/11.39  tff(f_122, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (m1_setfam_1(D, E) => m1_setfam_1(k6_funct_2(A, B, C, k7_funct_2(A, B, C, D)), E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_funct_2)).
% 20.91/11.39  tff(f_52, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 20.91/11.39  tff(f_98, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(A)))) => m1_subset_1(k7_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_funct_2)).
% 20.91/11.39  tff(f_82, axiom, (![A, B, C, D]: ((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(B)))) => m1_subset_1(k6_funct_2(A, B, C, D), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_funct_2)).
% 20.91/11.39  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.91/11.39  tff(c_56, plain, (![A_73, B_74]: (r1_tarski(A_73, B_74) | ~m1_subset_1(A_73, k1_zfmisc_1(B_74)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 20.91/11.39  tff(c_64, plain, (r1_tarski('#skF_7', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_56])).
% 20.91/11.39  tff(c_30, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 20.91/11.39  tff(c_18, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_tarski(k3_tarski(A_7), B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.91/11.39  tff(c_127, plain, (![C_94, A_95, B_96]: (r2_hidden(C_94, A_95) | ~r2_hidden(C_94, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 20.91/11.39  tff(c_970, plain, (![A_200, B_201, A_202]: (r2_hidden('#skF_3'(A_200, B_201), A_202) | ~m1_subset_1(A_200, k1_zfmisc_1(A_202)) | r1_tarski(k3_tarski(A_200), B_201))), inference(resolution, [status(thm)], [c_18, c_127])).
% 20.91/11.39  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.91/11.39  tff(c_2783, plain, (![A_331, B_332, A_333]: (r1_tarski('#skF_3'(A_331, B_332), A_333) | ~m1_subset_1(A_331, k1_zfmisc_1(k1_zfmisc_1(A_333))) | r1_tarski(k3_tarski(A_331), B_332))), inference(resolution, [status(thm)], [c_970, c_2])).
% 20.91/11.39  tff(c_2817, plain, (![A_335, B_336, A_337]: (r1_tarski('#skF_3'(A_335, B_336), A_337) | r1_tarski(k3_tarski(A_335), B_336) | ~r1_tarski(A_335, k1_zfmisc_1(A_337)))), inference(resolution, [status(thm)], [c_30, c_2783])).
% 20.91/11.39  tff(c_16, plain, (![A_7, B_8]: (~r1_tarski('#skF_3'(A_7, B_8), B_8) | r1_tarski(k3_tarski(A_7), B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.91/11.39  tff(c_2867, plain, (![A_335, A_337]: (r1_tarski(k3_tarski(A_335), A_337) | ~r1_tarski(A_335, k1_zfmisc_1(A_337)))), inference(resolution, [status(thm)], [c_2817, c_16])).
% 20.91/11.39  tff(c_54, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.91/11.39  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.91/11.39  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.91/11.39  tff(c_63, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_56])).
% 20.91/11.39  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.91/11.39  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.91/11.39  tff(c_14, plain, (![A_6]: (r1_tarski(A_6, k1_zfmisc_1(k3_tarski(A_6))))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.91/11.39  tff(c_93, plain, (![A_89, B_90]: (k5_setfam_1(A_89, B_90)=k3_tarski(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(A_89))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 20.91/11.39  tff(c_108, plain, (![A_91, A_92]: (k5_setfam_1(A_91, A_92)=k3_tarski(A_92) | ~r1_tarski(A_92, k1_zfmisc_1(A_91)))), inference(resolution, [status(thm)], [c_30, c_93])).
% 20.91/11.39  tff(c_117, plain, (![A_6]: (k5_setfam_1(k3_tarski(A_6), A_6)=k3_tarski(A_6))), inference(resolution, [status(thm)], [c_14, c_108])).
% 20.91/11.39  tff(c_223, plain, (![B_112, A_113]: (m1_setfam_1(B_112, A_113) | k5_setfam_1(A_113, B_112)!=A_113 | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(A_113))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.91/11.39  tff(c_443, plain, (![A_138, A_139]: (m1_setfam_1(A_138, A_139) | k5_setfam_1(A_139, A_138)!=A_139 | ~r1_tarski(A_138, k1_zfmisc_1(A_139)))), inference(resolution, [status(thm)], [c_30, c_223])).
% 20.91/11.39  tff(c_463, plain, (![A_6]: (m1_setfam_1(A_6, k3_tarski(A_6)) | k5_setfam_1(k3_tarski(A_6), A_6)!=k3_tarski(A_6))), inference(resolution, [status(thm)], [c_14, c_443])).
% 20.91/11.39  tff(c_472, plain, (![A_6]: (m1_setfam_1(A_6, k3_tarski(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_463])).
% 20.91/11.39  tff(c_901, plain, (![B_191, E_193, C_194, A_192, D_190]: (m1_setfam_1(k6_funct_2(A_192, B_191, C_194, k7_funct_2(A_192, B_191, C_194, D_190)), E_193) | ~m1_setfam_1(D_190, E_193) | ~m1_subset_1(E_193, k1_zfmisc_1(A_192)) | ~m1_subset_1(D_190, k1_zfmisc_1(k1_zfmisc_1(A_192))) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_191))) | ~v1_funct_2(C_194, A_192, B_191) | ~v1_funct_1(C_194) | v1_xboole_0(B_191) | v1_xboole_0(A_192))), inference(cnfTransformation, [status(thm)], [f_122])).
% 20.91/11.39  tff(c_3730, plain, (![C_406, B_408, A_409, E_410, A_407]: (m1_setfam_1(k6_funct_2(A_409, B_408, C_406, k7_funct_2(A_409, B_408, C_406, A_407)), E_410) | ~m1_setfam_1(A_407, E_410) | ~m1_subset_1(E_410, k1_zfmisc_1(A_409)) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(A_409, B_408))) | ~v1_funct_2(C_406, A_409, B_408) | ~v1_funct_1(C_406) | v1_xboole_0(B_408) | v1_xboole_0(A_409) | ~r1_tarski(A_407, k1_zfmisc_1(A_409)))), inference(resolution, [status(thm)], [c_30, c_901])).
% 20.91/11.39  tff(c_3736, plain, (![B_408, A_409, E_410, A_407, A_18]: (m1_setfam_1(k6_funct_2(A_409, B_408, A_18, k7_funct_2(A_409, B_408, A_18, A_407)), E_410) | ~m1_setfam_1(A_407, E_410) | ~m1_subset_1(E_410, k1_zfmisc_1(A_409)) | ~v1_funct_2(A_18, A_409, B_408) | ~v1_funct_1(A_18) | v1_xboole_0(B_408) | v1_xboole_0(A_409) | ~r1_tarski(A_407, k1_zfmisc_1(A_409)) | ~r1_tarski(A_18, k2_zfmisc_1(A_409, B_408)))), inference(resolution, [status(thm)], [c_30, c_3730])).
% 20.91/11.39  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, k3_tarski(B_15)) | ~m1_setfam_1(B_15, A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 20.91/11.39  tff(c_38, plain, (![A_26, B_27, C_28, D_29]: (m1_subset_1(k7_funct_2(A_26, B_27, C_28, D_29), k1_zfmisc_1(k1_zfmisc_1(B_27))) | ~m1_subset_1(D_29, k1_zfmisc_1(k1_zfmisc_1(A_26))) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_2(C_28, A_26, B_27) | ~v1_funct_1(C_28) | v1_xboole_0(B_27) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_98])).
% 20.91/11.39  tff(c_910, plain, (![B_191, C_194, E_193]: (m1_setfam_1(k6_funct_2('#skF_4', B_191, C_194, k7_funct_2('#skF_4', B_191, C_194, '#skF_7')), E_193) | ~m1_setfam_1('#skF_7', E_193) | ~m1_subset_1(E_193, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_191))) | ~v1_funct_2(C_194, '#skF_4', B_191) | ~v1_funct_1(C_194) | v1_xboole_0(B_191) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_901])).
% 20.91/11.39  tff(c_921, plain, (![B_196, C_197, E_198]: (m1_setfam_1(k6_funct_2('#skF_4', B_196, C_197, k7_funct_2('#skF_4', B_196, C_197, '#skF_7')), E_198) | ~m1_setfam_1('#skF_7', E_198) | ~m1_subset_1(E_198, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_196))) | ~v1_funct_2(C_197, '#skF_4', B_196) | ~v1_funct_1(C_197) | v1_xboole_0(B_196))), inference(negUnitSimplification, [status(thm)], [c_54, c_910])).
% 20.91/11.39  tff(c_926, plain, (![E_198]: (m1_setfam_1(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')), E_198) | ~m1_setfam_1('#skF_7', E_198) | ~m1_subset_1(E_198, k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_921])).
% 20.91/11.39  tff(c_930, plain, (![E_198]: (m1_setfam_1(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')), E_198) | ~m1_setfam_1('#skF_7', E_198) | ~m1_subset_1(E_198, k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_926])).
% 20.91/11.39  tff(c_931, plain, (![E_198]: (m1_setfam_1(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')), E_198) | ~m1_setfam_1('#skF_7', E_198) | ~m1_subset_1(E_198, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_930])).
% 20.91/11.39  tff(c_36, plain, (![A_22, B_23, C_24, D_25]: (m1_subset_1(k6_funct_2(A_22, B_23, C_24, D_25), k1_zfmisc_1(k1_zfmisc_1(A_22))) | ~m1_subset_1(D_25, k1_zfmisc_1(k1_zfmisc_1(B_23))) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24) | v1_xboole_0(B_23) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 20.91/11.39  tff(c_3888, plain, (![C_421, A_419, C_420, E_425, B_424, D_423, B_422]: (m1_setfam_1(k6_funct_2(A_419, B_422, C_420, k7_funct_2(A_419, B_422, C_420, k6_funct_2(A_419, B_424, C_421, D_423))), E_425) | ~m1_setfam_1(k6_funct_2(A_419, B_424, C_421, D_423), E_425) | ~m1_subset_1(E_425, k1_zfmisc_1(A_419)) | ~m1_subset_1(C_420, k1_zfmisc_1(k2_zfmisc_1(A_419, B_422))) | ~v1_funct_2(C_420, A_419, B_422) | ~v1_funct_1(C_420) | v1_xboole_0(B_422) | ~m1_subset_1(D_423, k1_zfmisc_1(k1_zfmisc_1(B_424))) | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(A_419, B_424))) | ~v1_funct_2(C_421, A_419, B_424) | ~v1_funct_1(C_421) | v1_xboole_0(B_424) | v1_xboole_0(A_419))), inference(resolution, [status(thm)], [c_36, c_901])).
% 20.91/11.39  tff(c_88, plain, (![A_87, B_88]: (~r1_tarski('#skF_3'(A_87, B_88), B_88) | r1_tarski(k3_tarski(A_87), B_88))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.91/11.39  tff(c_92, plain, (![A_87, B_15]: (r1_tarski(k3_tarski(A_87), k3_tarski(B_15)) | ~m1_setfam_1(B_15, '#skF_3'(A_87, k3_tarski(B_15))))), inference(resolution, [status(thm)], [c_22, c_88])).
% 20.91/11.39  tff(c_34766, plain, (![A_1713, C_1709, A_1712, B_1715, B_1714, D_1710, C_1711]: (r1_tarski(k3_tarski(A_1712), k3_tarski(k6_funct_2(A_1713, B_1715, C_1709, k7_funct_2(A_1713, B_1715, C_1709, k6_funct_2(A_1713, B_1714, C_1711, D_1710))))) | ~m1_setfam_1(k6_funct_2(A_1713, B_1714, C_1711, D_1710), '#skF_3'(A_1712, k3_tarski(k6_funct_2(A_1713, B_1715, C_1709, k7_funct_2(A_1713, B_1715, C_1709, k6_funct_2(A_1713, B_1714, C_1711, D_1710)))))) | ~m1_subset_1('#skF_3'(A_1712, k3_tarski(k6_funct_2(A_1713, B_1715, C_1709, k7_funct_2(A_1713, B_1715, C_1709, k6_funct_2(A_1713, B_1714, C_1711, D_1710))))), k1_zfmisc_1(A_1713)) | ~m1_subset_1(C_1709, k1_zfmisc_1(k2_zfmisc_1(A_1713, B_1715))) | ~v1_funct_2(C_1709, A_1713, B_1715) | ~v1_funct_1(C_1709) | v1_xboole_0(B_1715) | ~m1_subset_1(D_1710, k1_zfmisc_1(k1_zfmisc_1(B_1714))) | ~m1_subset_1(C_1711, k1_zfmisc_1(k2_zfmisc_1(A_1713, B_1714))) | ~v1_funct_2(C_1711, A_1713, B_1714) | ~v1_funct_1(C_1711) | v1_xboole_0(B_1714) | v1_xboole_0(A_1713))), inference(resolution, [status(thm)], [c_3888, c_92])).
% 20.91/11.39  tff(c_34814, plain, (![A_1712, B_1715, C_1709]: (r1_tarski(k3_tarski(A_1712), k3_tarski(k6_funct_2('#skF_4', B_1715, C_1709, k7_funct_2('#skF_4', B_1715, C_1709, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))) | ~m1_subset_1(C_1709, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1715))) | ~v1_funct_2(C_1709, '#skF_4', B_1715) | ~v1_funct_1(C_1709) | v1_xboole_0(B_1715) | ~m1_subset_1(k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | ~m1_setfam_1('#skF_7', '#skF_3'(A_1712, k3_tarski(k6_funct_2('#skF_4', B_1715, C_1709, k7_funct_2('#skF_4', B_1715, C_1709, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))))) | ~m1_subset_1('#skF_3'(A_1712, k3_tarski(k6_funct_2('#skF_4', B_1715, C_1709, k7_funct_2('#skF_4', B_1715, C_1709, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))), k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_931, c_34766])).
% 20.91/11.39  tff(c_34837, plain, (![A_1712, B_1715, C_1709]: (r1_tarski(k3_tarski(A_1712), k3_tarski(k6_funct_2('#skF_4', B_1715, C_1709, k7_funct_2('#skF_4', B_1715, C_1709, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))) | ~m1_subset_1(C_1709, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1715))) | ~v1_funct_2(C_1709, '#skF_4', B_1715) | ~v1_funct_1(C_1709) | v1_xboole_0(B_1715) | ~m1_subset_1(k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | ~m1_setfam_1('#skF_7', '#skF_3'(A_1712, k3_tarski(k6_funct_2('#skF_4', B_1715, C_1709, k7_funct_2('#skF_4', B_1715, C_1709, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))))) | ~m1_subset_1('#skF_3'(A_1712, k3_tarski(k6_funct_2('#skF_4', B_1715, C_1709, k7_funct_2('#skF_4', B_1715, C_1709, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_34814])).
% 20.91/11.39  tff(c_34838, plain, (![A_1712, B_1715, C_1709]: (r1_tarski(k3_tarski(A_1712), k3_tarski(k6_funct_2('#skF_4', B_1715, C_1709, k7_funct_2('#skF_4', B_1715, C_1709, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))) | ~m1_subset_1(C_1709, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1715))) | ~v1_funct_2(C_1709, '#skF_4', B_1715) | ~v1_funct_1(C_1709) | v1_xboole_0(B_1715) | ~m1_subset_1(k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) | ~m1_setfam_1('#skF_7', '#skF_3'(A_1712, k3_tarski(k6_funct_2('#skF_4', B_1715, C_1709, k7_funct_2('#skF_4', B_1715, C_1709, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))))) | ~m1_subset_1('#skF_3'(A_1712, k3_tarski(k6_funct_2('#skF_4', B_1715, C_1709, k7_funct_2('#skF_4', B_1715, C_1709, k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))))), k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_34837])).
% 20.91/11.39  tff(c_34894, plain, (~m1_subset_1(k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_34838])).
% 20.91/11.39  tff(c_34897, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_34894])).
% 20.91/11.39  tff(c_34903, plain, (v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_34897])).
% 20.91/11.39  tff(c_34905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_34903])).
% 20.91/11.39  tff(c_34907, plain, (m1_subset_1(k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_34838])).
% 20.91/11.39  tff(c_825, plain, (![A_176, B_177, C_178, D_179]: (m1_subset_1(k6_funct_2(A_176, B_177, C_178, D_179), k1_zfmisc_1(k1_zfmisc_1(A_176))) | ~m1_subset_1(D_179, k1_zfmisc_1(k1_zfmisc_1(B_177))) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_2(C_178, A_176, B_177) | ~v1_funct_1(C_178) | v1_xboole_0(B_177) | v1_xboole_0(A_176))), inference(cnfTransformation, [status(thm)], [f_82])).
% 20.91/11.39  tff(c_26, plain, (![A_16, B_17]: (k5_setfam_1(A_16, B_17)=k3_tarski(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 20.91/11.39  tff(c_840, plain, (![A_176, B_177, C_178, D_179]: (k5_setfam_1(A_176, k6_funct_2(A_176, B_177, C_178, D_179))=k3_tarski(k6_funct_2(A_176, B_177, C_178, D_179)) | ~m1_subset_1(D_179, k1_zfmisc_1(k1_zfmisc_1(B_177))) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_2(C_178, A_176, B_177) | ~v1_funct_1(C_178) | v1_xboole_0(B_177) | v1_xboole_0(A_176))), inference(resolution, [status(thm)], [c_825, c_26])).
% 20.91/11.39  tff(c_34943, plain, (![A_176, C_178]: (k5_setfam_1(A_176, k6_funct_2(A_176, '#skF_5', C_178, k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))=k3_tarski(k6_funct_2(A_176, '#skF_5', C_178, k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, '#skF_5'))) | ~v1_funct_2(C_178, A_176, '#skF_5') | ~v1_funct_1(C_178) | v1_xboole_0('#skF_5') | v1_xboole_0(A_176))), inference(resolution, [status(thm)], [c_34907, c_840])).
% 20.91/11.39  tff(c_35887, plain, (![A_1746, C_1747]: (k5_setfam_1(A_1746, k6_funct_2(A_1746, '#skF_5', C_1747, k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))=k3_tarski(k6_funct_2(A_1746, '#skF_5', C_1747, k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))) | ~m1_subset_1(C_1747, k1_zfmisc_1(k2_zfmisc_1(A_1746, '#skF_5'))) | ~v1_funct_2(C_1747, A_1746, '#skF_5') | ~v1_funct_1(C_1747) | v1_xboole_0(A_1746))), inference(negUnitSimplification, [status(thm)], [c_52, c_34943])).
% 20.91/11.39  tff(c_35892, plain, (k5_setfam_1('#skF_4', k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))=k3_tarski(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_35887])).
% 20.91/11.39  tff(c_35896, plain, (k5_setfam_1('#skF_4', k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))=k3_tarski(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_35892])).
% 20.91/11.39  tff(c_35897, plain, (k5_setfam_1('#skF_4', k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))=k3_tarski(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_54, c_35896])).
% 20.91/11.39  tff(c_102, plain, (k5_setfam_1('#skF_4', '#skF_7')=k3_tarski('#skF_7')), inference(resolution, [status(thm)], [c_44, c_93])).
% 20.91/11.39  tff(c_42, plain, (~r1_tarski(k5_setfam_1('#skF_4', '#skF_7'), k5_setfam_1('#skF_4', k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 20.91/11.39  tff(c_103, plain, (~r1_tarski(k3_tarski('#skF_7'), k5_setfam_1('#skF_4', k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_42])).
% 20.91/11.39  tff(c_36732, plain, (~r1_tarski(k3_tarski('#skF_7'), k3_tarski(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_35897, c_103])).
% 20.91/11.39  tff(c_36752, plain, (~m1_setfam_1(k6_funct_2('#skF_4', '#skF_5', '#skF_6', k7_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_7')), k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_22, c_36732])).
% 20.91/11.39  tff(c_36755, plain, (~m1_setfam_1('#skF_7', k3_tarski('#skF_7')) | ~m1_subset_1(k3_tarski('#skF_7'), k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | ~r1_tarski('#skF_7', k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_3736, c_36752])).
% 20.91/11.39  tff(c_36767, plain, (~m1_subset_1(k3_tarski('#skF_7'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_50, c_48, c_472, c_36755])).
% 20.91/11.39  tff(c_36768, plain, (~m1_subset_1(k3_tarski('#skF_7'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_36767])).
% 20.91/11.39  tff(c_36782, plain, (~r1_tarski(k3_tarski('#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_30, c_36768])).
% 20.91/11.39  tff(c_36794, plain, (~r1_tarski('#skF_7', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_2867, c_36782])).
% 20.91/11.39  tff(c_36807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_36794])).
% 20.91/11.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.91/11.39  
% 20.91/11.39  Inference rules
% 20.91/11.39  ----------------------
% 20.91/11.39  #Ref     : 0
% 20.91/11.39  #Sup     : 8092
% 20.91/11.39  #Fact    : 0
% 20.91/11.39  #Define  : 0
% 20.91/11.39  #Split   : 60
% 20.91/11.39  #Chain   : 0
% 20.91/11.39  #Close   : 0
% 20.91/11.39  
% 20.91/11.39  Ordering : KBO
% 20.91/11.39  
% 20.91/11.39  Simplification rules
% 20.91/11.39  ----------------------
% 20.91/11.39  #Subsume      : 1148
% 20.91/11.39  #Demod        : 1936
% 20.91/11.39  #Tautology    : 715
% 20.91/11.39  #SimpNegUnit  : 157
% 20.91/11.39  #BackRed      : 107
% 20.91/11.39  
% 20.91/11.39  #Partial instantiations: 0
% 20.91/11.39  #Strategies tried      : 1
% 20.91/11.39  
% 20.91/11.39  Timing (in seconds)
% 20.91/11.39  ----------------------
% 20.91/11.39  Preprocessing        : 0.34
% 20.91/11.39  Parsing              : 0.18
% 20.91/11.39  CNF conversion       : 0.03
% 20.91/11.40  Main loop            : 10.27
% 20.91/11.40  Inferencing          : 2.28
% 20.91/11.40  Reduction            : 3.31
% 20.91/11.40  Demodulation         : 2.36
% 20.91/11.40  BG Simplification    : 0.18
% 20.91/11.40  Subsumption          : 3.72
% 21.14/11.40  Abstraction          : 0.27
% 21.14/11.40  MUC search           : 0.00
% 21.14/11.40  Cooper               : 0.00
% 21.14/11.40  Total                : 10.65
% 21.14/11.40  Index Insertion      : 0.00
% 21.14/11.40  Index Deletion       : 0.00
% 21.14/11.40  Index Matching       : 0.00
% 21.14/11.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
