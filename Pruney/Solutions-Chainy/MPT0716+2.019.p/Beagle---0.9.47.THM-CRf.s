%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:39 EST 2020

% Result     : Theorem 9.26s
% Output     : CNFRefutation 9.26s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 485 expanded)
%              Number of leaves         :   29 ( 173 expanded)
%              Depth                    :   16
%              Number of atoms          :  236 (1349 expanded)
%              Number of equality atoms :   36 ( 110 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_22,plain,(
    ! [A_26,B_27] :
      ( v1_funct_1(k7_relat_1(A_26,B_27))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_79,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_51,B_52)),k1_relat_1(A_51))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_52,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [C_3] :
      ( r1_tarski('#skF_4',C_3)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_83,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_79,c_74])).

tff(c_89,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_83])).

tff(c_104,plain,(
    ! [B_54,A_55] :
      ( k1_relat_1(k7_relat_1(B_54,A_55)) = A_55
      | ~ r1_tarski(A_55,k1_relat_1(B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_107,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_89,c_104])).

tff(c_119,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_107])).

tff(c_18,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_23,A_22)),k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_135,plain,(
    ! [A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_4'),A_22)),'#skF_4')
      | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_18])).

tff(c_223,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_226,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_223])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_226])).

tff(c_232,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_238,plain,(
    ! [B_62,C_63,A_64] :
      ( k7_relat_1(k5_relat_1(B_62,C_63),A_64) = k5_relat_1(k7_relat_1(B_62,A_64),C_63)
      | ~ v1_relat_1(C_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_104])).

tff(c_162,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_165,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_165])).

tff(c_170,plain,(
    k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_247,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_170])).

tff(c_268,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_247])).

tff(c_12,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_633,plain,(
    ! [B_90,A_91] :
      ( r1_tarski(k2_relat_1(B_90),k1_relat_1(A_91))
      | k1_relat_1(k5_relat_1(B_90,A_91)) != k1_relat_1(B_90)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3452,plain,(
    ! [B_172,A_173,A_174] :
      ( r1_tarski(k9_relat_1(B_172,A_173),k1_relat_1(A_174))
      | k1_relat_1(k5_relat_1(k7_relat_1(B_172,A_173),A_174)) != k1_relat_1(k7_relat_1(B_172,A_173))
      | ~ v1_funct_1(k7_relat_1(B_172,A_173))
      | ~ v1_relat_1(k7_relat_1(B_172,A_173))
      | ~ v1_funct_1(A_174)
      | ~ v1_relat_1(A_174)
      | ~ v1_relat_1(B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_633])).

tff(c_40,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_221,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_40])).

tff(c_222,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_3458,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) != k1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3452,c_222])).

tff(c_3513,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_28,c_232,c_119,c_268,c_3458])).

tff(c_3524,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_3513])).

tff(c_3528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3524])).

tff(c_3530,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3574,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_36])).

tff(c_3575,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3574])).

tff(c_3587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3530,c_3575])).

tff(c_3588,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3574])).

tff(c_171,plain,(
    v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_3529,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_20,plain,(
    ! [B_25,A_24] :
      ( k1_relat_1(k7_relat_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3533,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3529,c_20])).

tff(c_3539,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3533])).

tff(c_3562,plain,(
    ! [A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_3'),A_22)),'#skF_3')
      | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3539,c_18])).

tff(c_4183,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3562])).

tff(c_4198,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_4183])).

tff(c_4202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4198])).

tff(c_4204,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3562])).

tff(c_38,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3664,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_3530,c_38])).

tff(c_3696,plain,(
    ! [A_178,B_179] :
      ( k1_relat_1(k5_relat_1(A_178,B_179)) = k1_relat_1(A_178)
      | ~ r1_tarski(k2_relat_1(A_178),k1_relat_1(B_179))
      | ~ v1_relat_1(B_179)
      | ~ v1_relat_1(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6571,plain,(
    ! [B_281,A_282,B_283] :
      ( k1_relat_1(k5_relat_1(k7_relat_1(B_281,A_282),B_283)) = k1_relat_1(k7_relat_1(B_281,A_282))
      | ~ r1_tarski(k9_relat_1(B_281,A_282),k1_relat_1(B_283))
      | ~ v1_relat_1(B_283)
      | ~ v1_relat_1(k7_relat_1(B_281,A_282))
      | ~ v1_relat_1(B_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3696])).

tff(c_6626,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = k1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3664,c_6571])).

tff(c_6656,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4204,c_30,c_3539,c_6626])).

tff(c_3601,plain,(
    ! [B_175,C_176,A_177] :
      ( k7_relat_1(k5_relat_1(B_175,C_176),A_177) = k5_relat_1(k7_relat_1(B_175,A_177),C_176)
      | ~ v1_relat_1(C_176)
      | ~ v1_relat_1(B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3616,plain,(
    ! [B_175,A_177,C_176] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_175,A_177),C_176)),k1_relat_1(k5_relat_1(B_175,C_176)))
      | ~ v1_relat_1(k5_relat_1(B_175,C_176))
      | ~ v1_relat_1(C_176)
      | ~ v1_relat_1(B_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3601,c_18])).

tff(c_6683,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6656,c_3616])).

tff(c_6732,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_171,c_6683])).

tff(c_6734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3588,c_6732])).

tff(c_6736,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6812,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6736,c_42])).

tff(c_6735,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6786,plain,(
    ! [B_293,A_294] :
      ( k1_relat_1(k7_relat_1(B_293,A_294)) = A_294
      | ~ r1_tarski(A_294,k1_relat_1(B_293))
      | ~ v1_relat_1(B_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6802,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6735,c_6786])).

tff(c_6811,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6802])).

tff(c_6825,plain,(
    ! [A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_3'),A_22)),'#skF_3')
      | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6811,c_18])).

tff(c_6879,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6825])).

tff(c_6882,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_6879])).

tff(c_6886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6882])).

tff(c_6888,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6825])).

tff(c_44,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6741,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_6736,c_44])).

tff(c_7098,plain,(
    ! [A_313,B_314] :
      ( k1_relat_1(k5_relat_1(A_313,B_314)) = k1_relat_1(A_313)
      | ~ r1_tarski(k2_relat_1(A_313),k1_relat_1(B_314))
      | ~ v1_relat_1(B_314)
      | ~ v1_relat_1(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_13108,plain,(
    ! [B_501,A_502,B_503] :
      ( k1_relat_1(k5_relat_1(k7_relat_1(B_501,A_502),B_503)) = k1_relat_1(k7_relat_1(B_501,A_502))
      | ~ r1_tarski(k9_relat_1(B_501,A_502),k1_relat_1(B_503))
      | ~ v1_relat_1(B_503)
      | ~ v1_relat_1(k7_relat_1(B_501,A_502))
      | ~ v1_relat_1(B_501) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_7098])).

tff(c_13152,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = k1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6741,c_13108])).

tff(c_13163,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6888,c_30,c_6811,c_13152])).

tff(c_6889,plain,(
    ! [B_297,C_298,A_299] :
      ( k7_relat_1(k5_relat_1(B_297,C_298),A_299) = k5_relat_1(k7_relat_1(B_297,A_299),C_298)
      | ~ v1_relat_1(C_298)
      | ~ v1_relat_1(B_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6901,plain,(
    ! [B_297,A_299,C_298] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_297,A_299),C_298)),k1_relat_1(k5_relat_1(B_297,C_298)))
      | ~ v1_relat_1(k5_relat_1(B_297,C_298))
      | ~ v1_relat_1(C_298)
      | ~ v1_relat_1(B_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6889,c_18])).

tff(c_13178,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13163,c_6901])).

tff(c_13262,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_13178])).

tff(c_13263,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_6812,c_13262])).

tff(c_13302,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_13263])).

tff(c_13306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_13302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:45:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.26/3.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.26/3.16  
% 9.26/3.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.26/3.17  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.26/3.17  
% 9.26/3.17  %Foreground sorts:
% 9.26/3.17  
% 9.26/3.17  
% 9.26/3.17  %Background operators:
% 9.26/3.17  
% 9.26/3.17  
% 9.26/3.17  %Foreground operators:
% 9.26/3.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.26/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.26/3.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.26/3.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.26/3.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.26/3.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.26/3.17  tff('#skF_2', type, '#skF_2': $i).
% 9.26/3.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.26/3.17  tff('#skF_3', type, '#skF_3': $i).
% 9.26/3.17  tff('#skF_1', type, '#skF_1': $i).
% 9.26/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.26/3.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.26/3.17  tff('#skF_4', type, '#skF_4': $i).
% 9.26/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.26/3.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.26/3.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.26/3.17  
% 9.26/3.19  tff(f_118, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 9.26/3.19  tff(f_39, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 9.26/3.19  tff(f_88, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 9.26/3.19  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.26/3.19  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 9.26/3.19  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.26/3.19  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 9.26/3.19  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 9.26/3.19  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 9.26/3.19  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 9.26/3.19  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 9.26/3.19  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 9.26/3.19  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 9.26/3.19  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.26/3.19  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.26/3.19  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.26/3.19  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.26/3.19  tff(c_22, plain, (![A_26, B_27]: (v1_funct_1(k7_relat_1(A_26, B_27)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.26/3.19  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.26/3.19  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.26/3.19  tff(c_79, plain, (![A_51, B_52]: (r1_tarski(k1_relat_1(k5_relat_1(A_51, B_52)), k1_relat_1(A_51)) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.26/3.19  tff(c_46, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.26/3.19  tff(c_52, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_46])).
% 9.26/3.19  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.26/3.19  tff(c_56, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_4])).
% 9.26/3.19  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.26/3.19  tff(c_74, plain, (![C_3]: (r1_tarski('#skF_4', C_3) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_3))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 9.26/3.19  tff(c_83, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_79, c_74])).
% 9.26/3.19  tff(c_89, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_83])).
% 9.26/3.19  tff(c_104, plain, (![B_54, A_55]: (k1_relat_1(k7_relat_1(B_54, A_55))=A_55 | ~r1_tarski(A_55, k1_relat_1(B_54)) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.26/3.19  tff(c_107, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_89, c_104])).
% 9.26/3.19  tff(c_119, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_107])).
% 9.26/3.19  tff(c_18, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(k7_relat_1(B_23, A_22)), k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.26/3.19  tff(c_135, plain, (![A_22]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), A_22)), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_119, c_18])).
% 9.26/3.19  tff(c_223, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_135])).
% 9.26/3.19  tff(c_226, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_223])).
% 9.26/3.19  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_226])).
% 9.26/3.19  tff(c_232, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitRight, [status(thm)], [c_135])).
% 9.26/3.19  tff(c_238, plain, (![B_62, C_63, A_64]: (k7_relat_1(k5_relat_1(B_62, C_63), A_64)=k5_relat_1(k7_relat_1(B_62, A_64), C_63) | ~v1_relat_1(C_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.26/3.19  tff(c_122, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4' | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_104])).
% 9.26/3.19  tff(c_162, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_122])).
% 9.26/3.19  tff(c_165, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_162])).
% 9.26/3.19  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_165])).
% 9.26/3.19  tff(c_170, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_122])).
% 9.26/3.19  tff(c_247, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_238, c_170])).
% 9.26/3.19  tff(c_268, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_247])).
% 9.26/3.19  tff(c_12, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.26/3.19  tff(c_633, plain, (![B_90, A_91]: (r1_tarski(k2_relat_1(B_90), k1_relat_1(A_91)) | k1_relat_1(k5_relat_1(B_90, A_91))!=k1_relat_1(B_90) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.26/3.19  tff(c_3452, plain, (![B_172, A_173, A_174]: (r1_tarski(k9_relat_1(B_172, A_173), k1_relat_1(A_174)) | k1_relat_1(k5_relat_1(k7_relat_1(B_172, A_173), A_174))!=k1_relat_1(k7_relat_1(B_172, A_173)) | ~v1_funct_1(k7_relat_1(B_172, A_173)) | ~v1_relat_1(k7_relat_1(B_172, A_173)) | ~v1_funct_1(A_174) | ~v1_relat_1(A_174) | ~v1_relat_1(B_172))), inference(superposition, [status(thm), theory('equality')], [c_12, c_633])).
% 9.26/3.19  tff(c_40, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.26/3.19  tff(c_221, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_40])).
% 9.26/3.19  tff(c_222, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_221])).
% 9.26/3.19  tff(c_3458, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))!=k1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3452, c_222])).
% 9.26/3.19  tff(c_3513, plain, (~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_28, c_232, c_119, c_268, c_3458])).
% 9.26/3.19  tff(c_3524, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_3513])).
% 9.26/3.19  tff(c_3528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3524])).
% 9.26/3.19  tff(c_3530, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_221])).
% 9.26/3.19  tff(c_36, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.26/3.19  tff(c_3574, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_36])).
% 9.26/3.19  tff(c_3575, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3574])).
% 9.26/3.19  tff(c_3587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3530, c_3575])).
% 9.26/3.19  tff(c_3588, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_3574])).
% 9.26/3.19  tff(c_171, plain, (v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_122])).
% 9.26/3.19  tff(c_3529, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_221])).
% 9.26/3.19  tff(c_20, plain, (![B_25, A_24]: (k1_relat_1(k7_relat_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.26/3.19  tff(c_3533, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3529, c_20])).
% 9.26/3.19  tff(c_3539, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3533])).
% 9.26/3.19  tff(c_3562, plain, (![A_22]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_3'), A_22)), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3539, c_18])).
% 9.26/3.19  tff(c_4183, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3562])).
% 9.26/3.19  tff(c_4198, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_4183])).
% 9.26/3.19  tff(c_4202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_4198])).
% 9.26/3.19  tff(c_4204, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_3562])).
% 9.26/3.19  tff(c_38, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.26/3.19  tff(c_3664, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_3530, c_38])).
% 9.26/3.19  tff(c_3696, plain, (![A_178, B_179]: (k1_relat_1(k5_relat_1(A_178, B_179))=k1_relat_1(A_178) | ~r1_tarski(k2_relat_1(A_178), k1_relat_1(B_179)) | ~v1_relat_1(B_179) | ~v1_relat_1(A_178))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.26/3.19  tff(c_6571, plain, (![B_281, A_282, B_283]: (k1_relat_1(k5_relat_1(k7_relat_1(B_281, A_282), B_283))=k1_relat_1(k7_relat_1(B_281, A_282)) | ~r1_tarski(k9_relat_1(B_281, A_282), k1_relat_1(B_283)) | ~v1_relat_1(B_283) | ~v1_relat_1(k7_relat_1(B_281, A_282)) | ~v1_relat_1(B_281))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3696])).
% 9.26/3.19  tff(c_6626, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))=k1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3664, c_6571])).
% 9.26/3.19  tff(c_6656, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4204, c_30, c_3539, c_6626])).
% 9.26/3.19  tff(c_3601, plain, (![B_175, C_176, A_177]: (k7_relat_1(k5_relat_1(B_175, C_176), A_177)=k5_relat_1(k7_relat_1(B_175, A_177), C_176) | ~v1_relat_1(C_176) | ~v1_relat_1(B_175))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.26/3.19  tff(c_3616, plain, (![B_175, A_177, C_176]: (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_175, A_177), C_176)), k1_relat_1(k5_relat_1(B_175, C_176))) | ~v1_relat_1(k5_relat_1(B_175, C_176)) | ~v1_relat_1(C_176) | ~v1_relat_1(B_175))), inference(superposition, [status(thm), theory('equality')], [c_3601, c_18])).
% 9.26/3.19  tff(c_6683, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6656, c_3616])).
% 9.26/3.19  tff(c_6732, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_171, c_6683])).
% 9.26/3.19  tff(c_6734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3588, c_6732])).
% 9.26/3.19  tff(c_6736, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_46])).
% 9.26/3.19  tff(c_42, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.26/3.19  tff(c_6812, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_6736, c_42])).
% 9.26/3.19  tff(c_6735, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_46])).
% 9.26/3.19  tff(c_6786, plain, (![B_293, A_294]: (k1_relat_1(k7_relat_1(B_293, A_294))=A_294 | ~r1_tarski(A_294, k1_relat_1(B_293)) | ~v1_relat_1(B_293))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.26/3.19  tff(c_6802, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6735, c_6786])).
% 9.26/3.19  tff(c_6811, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6802])).
% 9.26/3.19  tff(c_6825, plain, (![A_22]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_3'), A_22)), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6811, c_18])).
% 9.26/3.19  tff(c_6879, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_6825])).
% 9.26/3.19  tff(c_6882, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_6879])).
% 9.26/3.19  tff(c_6886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_6882])).
% 9.26/3.19  tff(c_6888, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_6825])).
% 9.26/3.19  tff(c_44, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.26/3.19  tff(c_6741, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_6736, c_44])).
% 9.26/3.19  tff(c_7098, plain, (![A_313, B_314]: (k1_relat_1(k5_relat_1(A_313, B_314))=k1_relat_1(A_313) | ~r1_tarski(k2_relat_1(A_313), k1_relat_1(B_314)) | ~v1_relat_1(B_314) | ~v1_relat_1(A_313))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.26/3.19  tff(c_13108, plain, (![B_501, A_502, B_503]: (k1_relat_1(k5_relat_1(k7_relat_1(B_501, A_502), B_503))=k1_relat_1(k7_relat_1(B_501, A_502)) | ~r1_tarski(k9_relat_1(B_501, A_502), k1_relat_1(B_503)) | ~v1_relat_1(B_503) | ~v1_relat_1(k7_relat_1(B_501, A_502)) | ~v1_relat_1(B_501))), inference(superposition, [status(thm), theory('equality')], [c_12, c_7098])).
% 9.26/3.19  tff(c_13152, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))=k1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6741, c_13108])).
% 9.26/3.19  tff(c_13163, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6888, c_30, c_6811, c_13152])).
% 9.26/3.19  tff(c_6889, plain, (![B_297, C_298, A_299]: (k7_relat_1(k5_relat_1(B_297, C_298), A_299)=k5_relat_1(k7_relat_1(B_297, A_299), C_298) | ~v1_relat_1(C_298) | ~v1_relat_1(B_297))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.26/3.19  tff(c_6901, plain, (![B_297, A_299, C_298]: (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_297, A_299), C_298)), k1_relat_1(k5_relat_1(B_297, C_298))) | ~v1_relat_1(k5_relat_1(B_297, C_298)) | ~v1_relat_1(C_298) | ~v1_relat_1(B_297))), inference(superposition, [status(thm), theory('equality')], [c_6889, c_18])).
% 9.26/3.19  tff(c_13178, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13163, c_6901])).
% 9.26/3.19  tff(c_13262, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_13178])).
% 9.26/3.19  tff(c_13263, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_6812, c_13262])).
% 9.26/3.19  tff(c_13302, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_13263])).
% 9.26/3.19  tff(c_13306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_13302])).
% 9.26/3.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.26/3.19  
% 9.26/3.19  Inference rules
% 9.26/3.19  ----------------------
% 9.26/3.19  #Ref     : 0
% 9.26/3.19  #Sup     : 3082
% 9.26/3.19  #Fact    : 0
% 9.26/3.19  #Define  : 0
% 9.26/3.19  #Split   : 18
% 9.26/3.19  #Chain   : 0
% 9.26/3.19  #Close   : 0
% 9.26/3.19  
% 9.26/3.19  Ordering : KBO
% 9.26/3.19  
% 9.26/3.19  Simplification rules
% 9.26/3.19  ----------------------
% 9.26/3.19  #Subsume      : 571
% 9.26/3.19  #Demod        : 1982
% 9.26/3.19  #Tautology    : 929
% 9.26/3.19  #SimpNegUnit  : 11
% 9.26/3.19  #BackRed      : 0
% 9.26/3.19  
% 9.26/3.19  #Partial instantiations: 0
% 9.26/3.19  #Strategies tried      : 1
% 9.26/3.19  
% 9.26/3.19  Timing (in seconds)
% 9.26/3.19  ----------------------
% 9.26/3.19  Preprocessing        : 0.32
% 9.26/3.19  Parsing              : 0.17
% 9.26/3.19  CNF conversion       : 0.02
% 9.26/3.19  Main loop            : 2.12
% 9.26/3.19  Inferencing          : 0.62
% 9.26/3.19  Reduction            : 0.73
% 9.26/3.19  Demodulation         : 0.53
% 9.26/3.19  BG Simplification    : 0.08
% 9.26/3.19  Subsumption          : 0.56
% 9.26/3.19  Abstraction          : 0.11
% 9.26/3.19  MUC search           : 0.00
% 9.26/3.19  Cooper               : 0.00
% 9.26/3.19  Total                : 2.48
% 9.26/3.19  Index Insertion      : 0.00
% 9.26/3.19  Index Deletion       : 0.00
% 9.26/3.19  Index Matching       : 0.00
% 9.26/3.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
