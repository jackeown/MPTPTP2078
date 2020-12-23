%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:34 EST 2020

% Result     : Theorem 24.07s
% Output     : CNFRefutation 24.20s
% Verified   : 
% Statistics : Number of formulae       :  239 (4831 expanded)
%              Number of leaves         :   34 (1679 expanded)
%              Depth                    :   32
%              Number of atoms          :  669 (14715 expanded)
%              Number of equality atoms :   50 (2361 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > v4_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_57,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ? [B] :
          ( v3_ordinal1(B)
          & r2_hidden(A,B)
          & v4_ordinal1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_ordinal1)).

tff(f_119,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_48,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_106,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_115,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(c_68,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12,plain,(
    ! [A_7] :
      ( v3_ordinal1('#skF_1'(A_7))
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_7] :
      ( r2_hidden(A_7,'#skF_1'(A_7))
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_66,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,(
    ! [A_39] :
      ( v2_wellord1(k1_wellord2(A_39))
      | ~ v3_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_62,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6,plain,(
    ! [B_6,A_4] :
      ( r2_hidden(B_6,A_4)
      | B_6 = A_4
      | r2_hidden(A_4,B_6)
      | ~ v3_ordinal1(B_6)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,(
    ! [A_35] : v1_relat_1(k1_wellord2(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_64,plain,(
    r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_99,plain,(
    ! [B_53,A_54] :
      ( r4_wellord1(B_53,A_54)
      | ~ r4_wellord1(A_54,B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_101,plain,
    ( r4_wellord1(k1_wellord2('#skF_7'),k1_wellord2('#skF_6'))
    | ~ v1_relat_1(k1_wellord2('#skF_7'))
    | ~ v1_relat_1(k1_wellord2('#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_99])).

tff(c_104,plain,(
    r4_wellord1(k1_wellord2('#skF_7'),k1_wellord2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_101])).

tff(c_60,plain,(
    ! [B_41,A_40] :
      ( k2_wellord1(k1_wellord2(B_41),A_40) = k1_wellord2(A_40)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    ! [A_27] :
      ( k3_relat_1(k1_wellord2(A_27)) = A_27
      | ~ v1_relat_1(k1_wellord2(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_74,plain,(
    ! [A_27] : k3_relat_1(k1_wellord2(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48])).

tff(c_56,plain,(
    ! [B_38,A_36] :
      ( k1_wellord1(k1_wellord2(B_38),A_36) = A_36
      | ~ r2_hidden(A_36,B_38)
      | ~ v3_ordinal1(B_38)
      | ~ v3_ordinal1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_337,plain,(
    ! [A_87,B_88] :
      ( ~ r4_wellord1(A_87,k2_wellord1(A_87,k1_wellord1(A_87,B_88)))
      | ~ r2_hidden(B_88,k3_relat_1(A_87))
      | ~ v2_wellord1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_340,plain,(
    ! [B_38,A_36] :
      ( ~ r4_wellord1(k1_wellord2(B_38),k2_wellord1(k1_wellord2(B_38),A_36))
      | ~ r2_hidden(A_36,k3_relat_1(k1_wellord2(B_38)))
      | ~ v2_wellord1(k1_wellord2(B_38))
      | ~ v1_relat_1(k1_wellord2(B_38))
      | ~ r2_hidden(A_36,B_38)
      | ~ v3_ordinal1(B_38)
      | ~ v3_ordinal1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_337])).

tff(c_562,plain,(
    ! [B_114,A_115] :
      ( ~ r4_wellord1(k1_wellord2(B_114),k2_wellord1(k1_wellord2(B_114),A_115))
      | ~ v2_wellord1(k1_wellord2(B_114))
      | ~ r2_hidden(A_115,B_114)
      | ~ v3_ordinal1(B_114)
      | ~ v3_ordinal1(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_340])).

tff(c_2029,plain,(
    ! [B_164,A_165] :
      ( ~ r4_wellord1(k1_wellord2(B_164),k1_wellord2(A_165))
      | ~ v2_wellord1(k1_wellord2(B_164))
      | ~ r2_hidden(A_165,B_164)
      | ~ v3_ordinal1(B_164)
      | ~ v3_ordinal1(A_165)
      | ~ r1_tarski(A_165,B_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_562])).

tff(c_2032,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_7'))
    | ~ r2_hidden('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_104,c_2029])).

tff(c_2038,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_7'))
    | ~ r2_hidden('#skF_6','#skF_7')
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2032])).

tff(c_2097,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2038])).

tff(c_344,plain,(
    ! [B_41,B_88] :
      ( ~ r4_wellord1(k1_wellord2(B_41),k1_wellord2(k1_wellord1(k1_wellord2(B_41),B_88)))
      | ~ r2_hidden(B_88,k3_relat_1(k1_wellord2(B_41)))
      | ~ v2_wellord1(k1_wellord2(B_41))
      | ~ v1_relat_1(k1_wellord2(B_41))
      | ~ r1_tarski(k1_wellord1(k1_wellord2(B_41),B_88),B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_337])).

tff(c_2260,plain,(
    ! [B_178,B_179] :
      ( ~ r4_wellord1(k1_wellord2(B_178),k1_wellord2(k1_wellord1(k1_wellord2(B_178),B_179)))
      | ~ r2_hidden(B_179,B_178)
      | ~ v2_wellord1(k1_wellord2(B_178))
      | ~ r1_tarski(k1_wellord1(k1_wellord2(B_178),B_179),B_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_344])).

tff(c_41960,plain,(
    ! [B_614,A_615] :
      ( ~ r4_wellord1(k1_wellord2(B_614),k1_wellord2(A_615))
      | ~ r2_hidden(A_615,B_614)
      | ~ v2_wellord1(k1_wellord2(B_614))
      | ~ r1_tarski(k1_wellord1(k1_wellord2(B_614),A_615),B_614)
      | ~ r2_hidden(A_615,B_614)
      | ~ v3_ordinal1(B_614)
      | ~ v3_ordinal1(A_615) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2260])).

tff(c_41962,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_7'))
    | ~ r1_tarski(k1_wellord1(k1_wellord2('#skF_7'),'#skF_6'),'#skF_7')
    | ~ r2_hidden('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_41960])).

tff(c_41967,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_7'))
    | ~ r1_tarski(k1_wellord1(k1_wellord2('#skF_7'),'#skF_6'),'#skF_7')
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_41962])).

tff(c_41971,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_41967])).

tff(c_2035,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_7','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_7')
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_2029])).

tff(c_2041,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_7','#skF_6')
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_2035])).

tff(c_2098,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2041])).

tff(c_41964,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r1_tarski(k1_wellord1(k1_wellord2('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_7','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_41960])).

tff(c_41970,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r1_tarski(k1_wellord1(k1_wellord2('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_41964])).

tff(c_41984,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_41970])).

tff(c_41999,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_41984])).

tff(c_42020,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_41999])).

tff(c_42022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41971,c_62,c_42020])).

tff(c_42024,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_41970])).

tff(c_206,plain,(
    ! [B_72,A_73] :
      ( k1_wellord1(k1_wellord2(B_72),A_73) = A_73
      | ~ r2_hidden(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_122,plain,(
    ! [D_61,B_62,A_63] :
      ( r2_hidden(k4_tarski(D_61,B_62),A_63)
      | ~ r2_hidden(D_61,k1_wellord1(A_63,B_62))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r2_hidden(A_1,k3_relat_1(C_3))
      | ~ r2_hidden(k4_tarski(A_1,B_2),C_3)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_133,plain,(
    ! [D_61,A_63,B_62] :
      ( r2_hidden(D_61,k3_relat_1(A_63))
      | ~ r2_hidden(D_61,k1_wellord1(A_63,B_62))
      | ~ v1_relat_1(A_63) ) ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_214,plain,(
    ! [D_61,B_72,A_73] :
      ( r2_hidden(D_61,k3_relat_1(k1_wellord2(B_72)))
      | ~ r2_hidden(D_61,A_73)
      | ~ v1_relat_1(k1_wellord2(B_72))
      | ~ r2_hidden(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_133])).

tff(c_258,plain,(
    ! [D_78,B_79,A_80] :
      ( r2_hidden(D_78,B_79)
      | ~ r2_hidden(D_78,A_80)
      | ~ r2_hidden(A_80,B_79)
      | ~ v3_ordinal1(B_79)
      | ~ v3_ordinal1(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_214])).

tff(c_274,plain,(
    ! [A_4,B_79,B_6] :
      ( r2_hidden(A_4,B_79)
      | ~ r2_hidden(B_6,B_79)
      | ~ v3_ordinal1(B_79)
      | r2_hidden(B_6,A_4)
      | B_6 = A_4
      | ~ v3_ordinal1(B_6)
      | ~ v3_ordinal1(A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_42043,plain,(
    ! [A_4] :
      ( r2_hidden(A_4,'#skF_6')
      | ~ v3_ordinal1('#skF_6')
      | r2_hidden('#skF_7',A_4)
      | A_4 = '#skF_7'
      | ~ v3_ordinal1('#skF_7')
      | ~ v3_ordinal1(A_4) ) ),
    inference(resolution,[status(thm)],[c_42024,c_274])).

tff(c_42878,plain,(
    ! [A_623] :
      ( r2_hidden(A_623,'#skF_6')
      | r2_hidden('#skF_7',A_623)
      | A_623 = '#skF_7'
      | ~ v3_ordinal1(A_623) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_42043])).

tff(c_566,plain,(
    ! [A_116,B_117,C_118] :
      ( r2_hidden(k4_tarski('#skF_2'(A_116,B_117,C_118),B_117),A_116)
      | r2_hidden('#skF_3'(A_116,B_117,C_118),C_118)
      | k1_wellord1(A_116,B_117) = C_118
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] :
      ( r2_hidden(B_2,k3_relat_1(C_3))
      | ~ r2_hidden(k4_tarski(A_1,B_2),C_3)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_620,plain,(
    ! [B_119,A_120,C_121] :
      ( r2_hidden(B_119,k3_relat_1(A_120))
      | r2_hidden('#skF_3'(A_120,B_119,C_121),C_121)
      | k1_wellord1(A_120,B_119) = C_121
      | ~ v1_relat_1(A_120) ) ),
    inference(resolution,[status(thm)],[c_566,c_2])).

tff(c_134,plain,(
    ! [B_62,A_63,D_61] :
      ( r2_hidden(B_62,k3_relat_1(A_63))
      | ~ r2_hidden(D_61,k1_wellord1(A_63,B_62))
      | ~ v1_relat_1(A_63) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_636,plain,(
    ! [B_62,A_63,B_119,A_120] :
      ( r2_hidden(B_62,k3_relat_1(A_63))
      | ~ v1_relat_1(A_63)
      | r2_hidden(B_119,k3_relat_1(A_120))
      | k1_wellord1(A_63,B_62) = k1_wellord1(A_120,B_119)
      | ~ v1_relat_1(A_120) ) ),
    inference(resolution,[status(thm)],[c_620,c_134])).

tff(c_851,plain,(
    ! [B_136,A_137,B_138,A_139] :
      ( r2_hidden(B_136,k3_relat_1(A_137))
      | ~ v1_relat_1(A_137)
      | r2_hidden(B_138,k3_relat_1(A_139))
      | k1_wellord1(A_139,B_138) = k1_wellord1(A_137,B_136)
      | ~ v1_relat_1(A_139) ) ),
    inference(resolution,[status(thm)],[c_620,c_134])).

tff(c_1022,plain,(
    ! [B_136,A_27,B_138,A_139] :
      ( r2_hidden(B_136,A_27)
      | ~ v1_relat_1(k1_wellord2(A_27))
      | r2_hidden(B_138,k3_relat_1(A_139))
      | k1_wellord1(k1_wellord2(A_27),B_136) = k1_wellord1(A_139,B_138)
      | ~ v1_relat_1(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_851])).

tff(c_1094,plain,(
    ! [B_143,A_144,B_145,A_146] :
      ( r2_hidden(B_143,A_144)
      | r2_hidden(B_145,k3_relat_1(A_146))
      | k1_wellord1(k1_wellord2(A_144),B_143) = k1_wellord1(A_146,B_145)
      | ~ v1_relat_1(A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1022])).

tff(c_1254,plain,(
    ! [B_143,A_144,B_145,A_27] :
      ( r2_hidden(B_143,A_144)
      | r2_hidden(B_145,A_27)
      | k1_wellord1(k1_wellord2(A_27),B_145) = k1_wellord1(k1_wellord2(A_144),B_143)
      | ~ v1_relat_1(k1_wellord2(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1094])).

tff(c_1303,plain,(
    ! [B_147,A_148,B_149,A_150] :
      ( r2_hidden(B_147,A_148)
      | r2_hidden(B_149,A_150)
      | k1_wellord1(k1_wellord2(A_150),B_149) = k1_wellord1(k1_wellord2(A_148),B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1254])).

tff(c_16,plain,(
    ! [D_20,B_16,A_9] :
      ( r2_hidden(k4_tarski(D_20,B_16),A_9)
      | ~ r2_hidden(D_20,k1_wellord1(A_9,B_16))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_142,plain,(
    ! [B_67,A_68,D_69] :
      ( r2_hidden(B_67,k3_relat_1(A_68))
      | ~ r2_hidden(D_69,k1_wellord1(A_68,B_67))
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_146,plain,(
    ! [B_67,A_68,D_20,B_16] :
      ( r2_hidden(B_67,k3_relat_1(A_68))
      | ~ v1_relat_1(A_68)
      | ~ r2_hidden(D_20,k1_wellord1(k1_wellord1(A_68,B_67),B_16))
      | ~ v1_relat_1(k1_wellord1(A_68,B_67)) ) ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_1345,plain,(
    ! [B_16,B_147,D_20,B_149,A_150,A_148] :
      ( r2_hidden(B_149,k3_relat_1(k1_wellord2(A_150)))
      | ~ v1_relat_1(k1_wellord2(A_150))
      | ~ r2_hidden(D_20,k1_wellord1(k1_wellord1(k1_wellord2(A_148),B_147),B_16))
      | ~ v1_relat_1(k1_wellord1(k1_wellord2(A_150),B_149))
      | r2_hidden(B_147,A_148)
      | r2_hidden(B_149,A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1303,c_146])).

tff(c_1457,plain,(
    ! [B_16,B_147,D_20,B_149,A_150,A_148] :
      ( ~ r2_hidden(D_20,k1_wellord1(k1_wellord1(k1_wellord2(A_148),B_147),B_16))
      | ~ v1_relat_1(k1_wellord1(k1_wellord2(A_150),B_149))
      | r2_hidden(B_147,A_148)
      | r2_hidden(B_149,A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_1345])).

tff(c_4887,plain,(
    ! [A_242,B_243] :
      ( ~ v1_relat_1(k1_wellord1(k1_wellord2(A_242),B_243))
      | r2_hidden(B_243,A_242) ) ),
    inference(splitLeft,[status(thm)],[c_1457])).

tff(c_4916,plain,(
    ! [A_63,B_62,B_119,A_242] :
      ( ~ v1_relat_1(k1_wellord1(A_63,B_62))
      | r2_hidden(B_119,A_242)
      | r2_hidden(B_62,k3_relat_1(A_63))
      | ~ v1_relat_1(A_63)
      | r2_hidden(B_119,k3_relat_1(k1_wellord2(A_242)))
      | ~ v1_relat_1(k1_wellord2(A_242)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_4887])).

tff(c_4927,plain,(
    ! [A_63,B_62,B_119,A_242] :
      ( ~ v1_relat_1(k1_wellord1(A_63,B_62))
      | r2_hidden(B_62,k3_relat_1(A_63))
      | ~ v1_relat_1(A_63)
      | r2_hidden(B_119,A_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_4916])).

tff(c_5045,plain,(
    ! [B_119,A_242] : r2_hidden(B_119,A_242) ),
    inference(splitLeft,[status(thm)],[c_4927])).

tff(c_18,plain,(
    ! [D_20,A_9] :
      ( ~ r2_hidden(D_20,k1_wellord1(A_9,D_20))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5148,plain,(
    ! [A_9] : ~ v1_relat_1(A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5045,c_18])).

tff(c_5152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5148,c_54])).

tff(c_5154,plain,(
    ! [A_249,B_250] :
      ( ~ v1_relat_1(k1_wellord1(A_249,B_250))
      | r2_hidden(B_250,k3_relat_1(A_249))
      | ~ v1_relat_1(A_249) ) ),
    inference(splitRight,[status(thm)],[c_4927])).

tff(c_225,plain,(
    ! [D_61,B_72,A_73] :
      ( r2_hidden(D_61,B_72)
      | ~ r2_hidden(D_61,A_73)
      | ~ r2_hidden(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_214])).

tff(c_6881,plain,(
    ! [B_295,B_296,A_297] :
      ( r2_hidden(B_295,B_296)
      | ~ r2_hidden(k3_relat_1(A_297),B_296)
      | ~ v3_ordinal1(B_296)
      | ~ v3_ordinal1(k3_relat_1(A_297))
      | ~ v1_relat_1(k1_wellord1(A_297,B_295))
      | ~ v1_relat_1(A_297) ) ),
    inference(resolution,[status(thm)],[c_5154,c_225])).

tff(c_6955,plain,(
    ! [B_295,B_296,A_27] :
      ( r2_hidden(B_295,B_296)
      | ~ r2_hidden(A_27,B_296)
      | ~ v3_ordinal1(B_296)
      | ~ v3_ordinal1(k3_relat_1(k1_wellord2(A_27)))
      | ~ v1_relat_1(k1_wellord1(k1_wellord2(A_27),B_295))
      | ~ v1_relat_1(k1_wellord2(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_6881])).

tff(c_6982,plain,(
    ! [B_298,B_299,A_300] :
      ( r2_hidden(B_298,B_299)
      | ~ r2_hidden(A_300,B_299)
      | ~ v3_ordinal1(B_299)
      | ~ v3_ordinal1(A_300)
      | ~ v1_relat_1(k1_wellord1(k1_wellord2(A_300),B_298)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_6955])).

tff(c_7109,plain,(
    ! [B_301,A_302] :
      ( r2_hidden(B_301,'#skF_1'(A_302))
      | ~ v3_ordinal1('#skF_1'(A_302))
      | ~ v1_relat_1(k1_wellord1(k1_wellord2(A_302),B_301))
      | ~ v3_ordinal1(A_302) ) ),
    inference(resolution,[status(thm)],[c_10,c_6982])).

tff(c_7447,plain,(
    ! [A_311,B_312] :
      ( r2_hidden(A_311,'#skF_1'(B_312))
      | ~ v3_ordinal1('#skF_1'(B_312))
      | ~ v1_relat_1(A_311)
      | ~ v3_ordinal1(B_312)
      | ~ r2_hidden(A_311,B_312)
      | ~ v3_ordinal1(B_312)
      | ~ v3_ordinal1(A_311) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_7109])).

tff(c_217,plain,(
    ! [A_73,B_72] :
      ( ~ r2_hidden(A_73,A_73)
      | ~ v1_relat_1(k1_wellord2(B_72))
      | ~ r2_hidden(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_18])).

tff(c_227,plain,(
    ! [A_73,B_72] :
      ( ~ r2_hidden(A_73,A_73)
      | ~ r2_hidden(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_217])).

tff(c_5315,plain,(
    ! [A_257,B_258] :
      ( ~ r2_hidden(k3_relat_1(A_257),B_258)
      | ~ v3_ordinal1(B_258)
      | ~ v3_ordinal1(k3_relat_1(A_257))
      | ~ v1_relat_1(k1_wellord1(A_257,k3_relat_1(A_257)))
      | ~ v1_relat_1(A_257) ) ),
    inference(resolution,[status(thm)],[c_5154,c_227])).

tff(c_5573,plain,(
    ! [A_262] :
      ( ~ v3_ordinal1('#skF_1'(k3_relat_1(A_262)))
      | ~ v1_relat_1(k1_wellord1(A_262,k3_relat_1(A_262)))
      | ~ v1_relat_1(A_262)
      | ~ v3_ordinal1(k3_relat_1(A_262)) ) ),
    inference(resolution,[status(thm)],[c_10,c_5315])).

tff(c_5582,plain,(
    ! [A_263] :
      ( ~ v1_relat_1(k1_wellord1(A_263,k3_relat_1(A_263)))
      | ~ v1_relat_1(A_263)
      | ~ v3_ordinal1(k3_relat_1(A_263)) ) ),
    inference(resolution,[status(thm)],[c_12,c_5573])).

tff(c_5626,plain,(
    ! [B_38] :
      ( ~ v1_relat_1(k3_relat_1(k1_wellord2(B_38)))
      | ~ v1_relat_1(k1_wellord2(B_38))
      | ~ v3_ordinal1(k3_relat_1(k1_wellord2(B_38)))
      | ~ r2_hidden(k3_relat_1(k1_wellord2(B_38)),B_38)
      | ~ v3_ordinal1(B_38)
      | ~ v3_ordinal1(k3_relat_1(k1_wellord2(B_38))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_5582])).

tff(c_5645,plain,(
    ! [B_38] :
      ( ~ v1_relat_1(B_38)
      | ~ r2_hidden(B_38,B_38)
      | ~ v3_ordinal1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_74,c_54,c_74,c_5626])).

tff(c_7503,plain,(
    ! [B_312] :
      ( ~ v1_relat_1('#skF_1'(B_312))
      | ~ r2_hidden('#skF_1'(B_312),B_312)
      | ~ v3_ordinal1(B_312)
      | ~ v3_ordinal1('#skF_1'(B_312)) ) ),
    inference(resolution,[status(thm)],[c_7447,c_5645])).

tff(c_42925,plain,
    ( ~ v1_relat_1('#skF_1'('#skF_6'))
    | ~ v3_ordinal1('#skF_6')
    | r2_hidden('#skF_7','#skF_1'('#skF_6'))
    | '#skF_1'('#skF_6') = '#skF_7'
    | ~ v3_ordinal1('#skF_1'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_42878,c_7503])).

tff(c_43076,plain,
    ( ~ v1_relat_1('#skF_1'('#skF_6'))
    | r2_hidden('#skF_7','#skF_1'('#skF_6'))
    | '#skF_1'('#skF_6') = '#skF_7'
    | ~ v3_ordinal1('#skF_1'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_42925])).

tff(c_44677,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_43076])).

tff(c_45013,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_44677])).

tff(c_45017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_45013])).

tff(c_45019,plain,(
    v3_ordinal1('#skF_1'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_43076])).

tff(c_42963,plain,(
    ! [A_623,B_72] :
      ( r2_hidden(A_623,B_72)
      | ~ r2_hidden('#skF_6',B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1('#skF_6')
      | r2_hidden('#skF_7',A_623)
      | A_623 = '#skF_7'
      | ~ v3_ordinal1(A_623) ) ),
    inference(resolution,[status(thm)],[c_42878,c_225])).

tff(c_46121,plain,(
    ! [A_651,B_652] :
      ( r2_hidden(A_651,B_652)
      | ~ r2_hidden('#skF_6',B_652)
      | ~ v3_ordinal1(B_652)
      | r2_hidden('#skF_7',A_651)
      | A_651 = '#skF_7'
      | ~ v3_ordinal1(A_651) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_42963])).

tff(c_46246,plain,(
    ! [A_651] :
      ( r2_hidden(A_651,'#skF_1'('#skF_6'))
      | ~ v3_ordinal1('#skF_1'('#skF_6'))
      | r2_hidden('#skF_7',A_651)
      | A_651 = '#skF_7'
      | ~ v3_ordinal1(A_651)
      | ~ v3_ordinal1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10,c_46121])).

tff(c_46335,plain,(
    ! [A_653] :
      ( r2_hidden(A_653,'#skF_1'('#skF_6'))
      | r2_hidden('#skF_7',A_653)
      | A_653 = '#skF_7'
      | ~ v3_ordinal1(A_653) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_45019,c_46246])).

tff(c_46436,plain,(
    ! [B_72] :
      ( ~ r2_hidden('#skF_1'('#skF_6'),B_72)
      | ~ v3_ordinal1(B_72)
      | r2_hidden('#skF_7','#skF_1'('#skF_6'))
      | '#skF_1'('#skF_6') = '#skF_7'
      | ~ v3_ordinal1('#skF_1'('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_46335,c_227])).

tff(c_46529,plain,(
    ! [B_72] :
      ( ~ r2_hidden('#skF_1'('#skF_6'),B_72)
      | ~ v3_ordinal1(B_72)
      | r2_hidden('#skF_7','#skF_1'('#skF_6'))
      | '#skF_1'('#skF_6') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45019,c_46436])).

tff(c_46533,plain,(
    ! [B_654] :
      ( ~ r2_hidden('#skF_1'('#skF_6'),B_654)
      | ~ v3_ordinal1(B_654) ) ),
    inference(splitLeft,[status(thm)],[c_46529])).

tff(c_46707,plain,
    ( ~ v3_ordinal1('#skF_1'('#skF_1'('#skF_6')))
    | ~ v3_ordinal1('#skF_1'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_10,c_46533])).

tff(c_46800,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_1'('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45019,c_46707])).

tff(c_46803,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_12,c_46800])).

tff(c_46807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45019,c_46803])).

tff(c_46808,plain,
    ( '#skF_1'('#skF_6') = '#skF_7'
    | r2_hidden('#skF_7','#skF_1'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_46529])).

tff(c_46809,plain,(
    r2_hidden('#skF_7','#skF_1'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_46808])).

tff(c_52,plain,(
    ! [C_33,D_34,A_27] :
      ( r1_tarski(C_33,D_34)
      | ~ r2_hidden(k4_tarski(C_33,D_34),k1_wellord2(A_27))
      | ~ r2_hidden(D_34,A_27)
      | ~ r2_hidden(C_33,A_27)
      | ~ v1_relat_1(k1_wellord2(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_362,plain,(
    ! [C_92,D_93,A_94] :
      ( r1_tarski(C_92,D_93)
      | ~ r2_hidden(k4_tarski(C_92,D_93),k1_wellord2(A_94))
      | ~ r2_hidden(D_93,A_94)
      | ~ r2_hidden(C_92,A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52])).

tff(c_372,plain,(
    ! [D_20,B_16,A_94] :
      ( r1_tarski(D_20,B_16)
      | ~ r2_hidden(B_16,A_94)
      | ~ r2_hidden(D_20,A_94)
      | ~ r2_hidden(D_20,k1_wellord1(k1_wellord2(A_94),B_16))
      | ~ v1_relat_1(k1_wellord2(A_94)) ) ),
    inference(resolution,[status(thm)],[c_16,c_362])).

tff(c_404,plain,(
    ! [D_98,B_99,A_100] :
      ( r1_tarski(D_98,B_99)
      | ~ r2_hidden(B_99,A_100)
      | ~ r2_hidden(D_98,A_100)
      | ~ r2_hidden(D_98,k1_wellord1(k1_wellord2(A_100),B_99)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_372])).

tff(c_3504,plain,(
    ! [D_209,A_210,B_211] :
      ( r1_tarski(D_209,A_210)
      | ~ r2_hidden(A_210,B_211)
      | ~ r2_hidden(D_209,B_211)
      | ~ r2_hidden(D_209,A_210)
      | ~ r2_hidden(A_210,B_211)
      | ~ v3_ordinal1(B_211)
      | ~ v3_ordinal1(A_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_404])).

tff(c_3591,plain,(
    ! [D_209,A_7] :
      ( r1_tarski(D_209,A_7)
      | ~ r2_hidden(D_209,'#skF_1'(A_7))
      | ~ r2_hidden(D_209,A_7)
      | ~ r2_hidden(A_7,'#skF_1'(A_7))
      | ~ v3_ordinal1('#skF_1'(A_7))
      | ~ v3_ordinal1(A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_3504])).

tff(c_46832,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_6')
    | ~ r2_hidden('#skF_6','#skF_1'('#skF_6'))
    | ~ v3_ordinal1('#skF_1'('#skF_6'))
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46809,c_3591])).

tff(c_46873,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | ~ r2_hidden('#skF_6','#skF_1'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_45019,c_42024,c_46832])).

tff(c_46874,plain,(
    ~ r2_hidden('#skF_6','#skF_1'('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_2098,c_46873])).

tff(c_46997,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_46874])).

tff(c_47021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46997])).

tff(c_47022,plain,(
    '#skF_1'('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_46808])).

tff(c_47126,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_47022,c_10])).

tff(c_47204,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_47126])).

tff(c_47206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41971,c_47204])).

tff(c_47208,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_41967])).

tff(c_47229,plain,(
    ! [B_72] :
      ( r2_hidden('#skF_6',B_72)
      | ~ r2_hidden('#skF_7',B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_47208,c_225])).

tff(c_47303,plain,(
    ! [B_658] :
      ( r2_hidden('#skF_6',B_658)
      | ~ r2_hidden('#skF_7',B_658)
      | ~ v3_ordinal1(B_658) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_47229])).

tff(c_47465,plain,
    ( r2_hidden('#skF_6','#skF_1'('#skF_7'))
    | ~ v3_ordinal1('#skF_1'('#skF_7'))
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_47303])).

tff(c_47549,plain,
    ( r2_hidden('#skF_6','#skF_1'('#skF_7'))
    | ~ v3_ordinal1('#skF_1'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_47465])).

tff(c_47550,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_47549])).

tff(c_47553,plain,(
    ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_47550])).

tff(c_47557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_47553])).

tff(c_47559,plain,(
    v3_ordinal1('#skF_1'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_47549])).

tff(c_47558,plain,(
    r2_hidden('#skF_6','#skF_1'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_47549])).

tff(c_47898,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_7','#skF_1'('#skF_7'))
    | ~ v3_ordinal1('#skF_1'('#skF_7'))
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_47558,c_3591])).

tff(c_47932,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_7','#skF_1'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_47559,c_47208,c_47898])).

tff(c_47933,plain,(
    ~ r2_hidden('#skF_7','#skF_1'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_2097,c_47932])).

tff(c_47967,plain,(
    ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_47933])).

tff(c_47988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_47967])).

tff(c_47989,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2041])).

tff(c_47991,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_47989])).

tff(c_47994,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_47991])).

tff(c_47998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_47994])).

tff(c_47999,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_47989])).

tff(c_48003,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_47999])).

tff(c_48009,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_48003])).

tff(c_48010,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_48009])).

tff(c_48018,plain,(
    ! [B_72] :
      ( r2_hidden('#skF_6',B_72)
      | ~ r2_hidden('#skF_7',B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48010,c_225])).

tff(c_48078,plain,(
    ! [B_665] :
      ( r2_hidden('#skF_6',B_665)
      | ~ r2_hidden('#skF_7',B_665)
      | ~ v3_ordinal1(B_665) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_48018])).

tff(c_48130,plain,
    ( r2_hidden('#skF_6','#skF_1'('#skF_7'))
    | ~ v3_ordinal1('#skF_1'('#skF_7'))
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_48078])).

tff(c_48155,plain,
    ( r2_hidden('#skF_6','#skF_1'('#skF_7'))
    | ~ v3_ordinal1('#skF_1'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_48130])).

tff(c_48156,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_48155])).

tff(c_48159,plain,(
    ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_48156])).

tff(c_48163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_48159])).

tff(c_48165,plain,(
    v3_ordinal1('#skF_1'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48155])).

tff(c_48164,plain,(
    r2_hidden('#skF_6','#skF_1'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48155])).

tff(c_48260,plain,(
    ! [B_72] :
      ( r2_hidden('#skF_6',B_72)
      | ~ r2_hidden('#skF_1'('#skF_7'),B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1('#skF_1'('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_48164,c_225])).

tff(c_48267,plain,(
    ! [B_667] :
      ( r2_hidden('#skF_6',B_667)
      | ~ r2_hidden('#skF_1'('#skF_7'),B_667)
      | ~ v3_ordinal1(B_667) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48165,c_48260])).

tff(c_48323,plain,
    ( r2_hidden('#skF_6','#skF_1'('#skF_1'('#skF_7')))
    | ~ v3_ordinal1('#skF_1'('#skF_1'('#skF_7')))
    | ~ v3_ordinal1('#skF_1'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_10,c_48267])).

tff(c_48351,plain,
    ( r2_hidden('#skF_6','#skF_1'('#skF_1'('#skF_7')))
    | ~ v3_ordinal1('#skF_1'('#skF_1'('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48165,c_48323])).

tff(c_48352,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_1'('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_48351])).

tff(c_48355,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_12,c_48352])).

tff(c_48359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48165,c_48355])).

tff(c_48361,plain,(
    v3_ordinal1('#skF_1'('#skF_1'('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_48351])).

tff(c_48360,plain,(
    r2_hidden('#skF_6','#skF_1'('#skF_1'('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_48351])).

tff(c_297,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(A_84,B_85)
      | ~ r2_hidden('#skF_1'(A_84),B_85)
      | ~ v3_ordinal1(B_85)
      | ~ v3_ordinal1('#skF_1'(A_84))
      | ~ v3_ordinal1(A_84) ) ),
    inference(resolution,[status(thm)],[c_10,c_258])).

tff(c_312,plain,(
    ! [A_84] :
      ( r2_hidden(A_84,'#skF_1'('#skF_1'(A_84)))
      | ~ v3_ordinal1('#skF_1'('#skF_1'(A_84)))
      | ~ v3_ordinal1(A_84)
      | ~ v3_ordinal1('#skF_1'(A_84)) ) ),
    inference(resolution,[status(thm)],[c_10,c_297])).

tff(c_47990,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2041])).

tff(c_50,plain,(
    ! [C_33,D_34,A_27] :
      ( r2_hidden(k4_tarski(C_33,D_34),k1_wellord2(A_27))
      | ~ r1_tarski(C_33,D_34)
      | ~ r2_hidden(D_34,A_27)
      | ~ r2_hidden(C_33,A_27)
      | ~ v1_relat_1(k1_wellord2(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_378,plain,(
    ! [C_95,D_96,A_97] :
      ( r2_hidden(k4_tarski(C_95,D_96),k1_wellord2(A_97))
      | ~ r1_tarski(C_95,D_96)
      | ~ r2_hidden(D_96,A_97)
      | ~ r2_hidden(C_95,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50])).

tff(c_14,plain,(
    ! [D_20,A_9,B_16] :
      ( r2_hidden(D_20,k1_wellord1(A_9,B_16))
      | ~ r2_hidden(k4_tarski(D_20,B_16),A_9)
      | D_20 = B_16
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_384,plain,(
    ! [C_95,A_97,D_96] :
      ( r2_hidden(C_95,k1_wellord1(k1_wellord2(A_97),D_96))
      | D_96 = C_95
      | ~ v1_relat_1(k1_wellord2(A_97))
      | ~ r1_tarski(C_95,D_96)
      | ~ r2_hidden(D_96,A_97)
      | ~ r2_hidden(C_95,A_97) ) ),
    inference(resolution,[status(thm)],[c_378,c_14])).

tff(c_396,plain,(
    ! [C_95,A_97,D_96] :
      ( r2_hidden(C_95,k1_wellord1(k1_wellord2(A_97),D_96))
      | D_96 = C_95
      | ~ r1_tarski(C_95,D_96)
      | ~ r2_hidden(D_96,A_97)
      | ~ r2_hidden(C_95,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_384])).

tff(c_54298,plain,(
    ! [A_740,D_741] :
      ( r2_hidden('#skF_6',k1_wellord1(k1_wellord2(A_740),D_741))
      | ~ v3_ordinal1(k1_wellord1(k1_wellord2(A_740),D_741))
      | D_741 = '#skF_7'
      | ~ r1_tarski('#skF_7',D_741)
      | ~ r2_hidden(D_741,A_740)
      | ~ r2_hidden('#skF_7',A_740) ) ),
    inference(resolution,[status(thm)],[c_396,c_48078])).

tff(c_54325,plain,(
    ! [A_740] :
      ( ~ v1_relat_1(k1_wellord2(A_740))
      | ~ v3_ordinal1(k1_wellord1(k1_wellord2(A_740),'#skF_6'))
      | '#skF_7' = '#skF_6'
      | ~ r1_tarski('#skF_7','#skF_6')
      | ~ r2_hidden('#skF_6',A_740)
      | ~ r2_hidden('#skF_7',A_740) ) ),
    inference(resolution,[status(thm)],[c_54298,c_18])).

tff(c_54405,plain,(
    ! [A_740] :
      ( ~ v3_ordinal1(k1_wellord1(k1_wellord2(A_740),'#skF_6'))
      | '#skF_7' = '#skF_6'
      | ~ r2_hidden('#skF_6',A_740)
      | ~ r2_hidden('#skF_7',A_740) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47990,c_54,c_54325])).

tff(c_54419,plain,(
    ! [A_742] :
      ( ~ v3_ordinal1(k1_wellord1(k1_wellord2(A_742),'#skF_6'))
      | ~ r2_hidden('#skF_6',A_742)
      | ~ r2_hidden('#skF_7',A_742) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54405])).

tff(c_54467,plain,(
    ! [B_38] :
      ( ~ v3_ordinal1('#skF_6')
      | ~ r2_hidden('#skF_6',B_38)
      | ~ r2_hidden('#skF_7',B_38)
      | ~ r2_hidden('#skF_6',B_38)
      | ~ v3_ordinal1(B_38)
      | ~ v3_ordinal1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_54419])).

tff(c_54478,plain,(
    ! [B_743] :
      ( ~ r2_hidden('#skF_7',B_743)
      | ~ r2_hidden('#skF_6',B_743)
      | ~ v3_ordinal1(B_743) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_54467])).

tff(c_54598,plain,
    ( ~ r2_hidden('#skF_6','#skF_1'('#skF_1'('#skF_7')))
    | ~ v3_ordinal1('#skF_1'('#skF_1'('#skF_7')))
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_1'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_312,c_54478])).

tff(c_54688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48165,c_66,c_48361,c_48360,c_54598])).

tff(c_54689,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ v2_wellord1(k1_wellord2('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2038])).

tff(c_54691,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_54689])).

tff(c_54694,plain,(
    ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_54691])).

tff(c_54698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54694])).

tff(c_54699,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54689])).

tff(c_55913,plain,(
    ! [B_776,B_777] :
      ( ~ r4_wellord1(k1_wellord2(B_776),k1_wellord2(k1_wellord1(k1_wellord2(B_776),B_777)))
      | ~ r2_hidden(B_777,B_776)
      | ~ v2_wellord1(k1_wellord2(B_776))
      | ~ r1_tarski(k1_wellord1(k1_wellord2(B_776),B_777),B_776) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_344])).

tff(c_102788,plain,(
    ! [B_1220,A_1221] :
      ( ~ r4_wellord1(k1_wellord2(B_1220),k1_wellord2(A_1221))
      | ~ r2_hidden(A_1221,B_1220)
      | ~ v2_wellord1(k1_wellord2(B_1220))
      | ~ r1_tarski(k1_wellord1(k1_wellord2(B_1220),A_1221),B_1220)
      | ~ r2_hidden(A_1221,B_1220)
      | ~ v3_ordinal1(B_1220)
      | ~ v3_ordinal1(A_1221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_55913])).

tff(c_102792,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r1_tarski(k1_wellord1(k1_wellord2('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_7','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_102788])).

tff(c_102798,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r1_tarski(k1_wellord1(k1_wellord2('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_102792])).

tff(c_102799,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_102798])).

tff(c_102832,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_102799])).

tff(c_102875,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_102832])).

tff(c_102877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54699,c_62,c_102875])).

tff(c_102879,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_102798])).

tff(c_102900,plain,(
    ! [B_72] :
      ( r2_hidden('#skF_7',B_72)
      | ~ r2_hidden('#skF_6',B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_102879,c_225])).

tff(c_102931,plain,(
    ! [B_72] :
      ( r2_hidden('#skF_7',B_72)
      | ~ r2_hidden('#skF_6',B_72)
      | ~ v3_ordinal1(B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102900])).

tff(c_54690,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2038])).

tff(c_102987,plain,(
    ! [B_1222] :
      ( r2_hidden('#skF_7',B_1222)
      | ~ r2_hidden('#skF_6',B_1222)
      | ~ v3_ordinal1(B_1222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102900])).

tff(c_104484,plain,(
    ! [A_1229] :
      ( ~ v1_relat_1(A_1229)
      | ~ r2_hidden('#skF_6',k1_wellord1(A_1229,'#skF_7'))
      | ~ v3_ordinal1(k1_wellord1(A_1229,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_102987,c_18])).

tff(c_104685,plain,(
    ! [A_97] :
      ( ~ v1_relat_1(k1_wellord2(A_97))
      | ~ v3_ordinal1(k1_wellord1(k1_wellord2(A_97),'#skF_7'))
      | '#skF_7' = '#skF_6'
      | ~ r1_tarski('#skF_6','#skF_7')
      | ~ r2_hidden('#skF_7',A_97)
      | ~ r2_hidden('#skF_6',A_97) ) ),
    inference(resolution,[status(thm)],[c_396,c_104484])).

tff(c_104783,plain,(
    ! [A_97] :
      ( ~ v3_ordinal1(k1_wellord1(k1_wellord2(A_97),'#skF_7'))
      | '#skF_7' = '#skF_6'
      | ~ r2_hidden('#skF_7',A_97)
      | ~ r2_hidden('#skF_6',A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54690,c_54,c_104685])).

tff(c_104787,plain,(
    ! [A_1230] :
      ( ~ v3_ordinal1(k1_wellord1(k1_wellord2(A_1230),'#skF_7'))
      | ~ r2_hidden('#skF_7',A_1230)
      | ~ r2_hidden('#skF_6',A_1230) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_104783])).

tff(c_104950,plain,(
    ! [B_38] :
      ( ~ v3_ordinal1('#skF_7')
      | ~ r2_hidden('#skF_7',B_38)
      | ~ r2_hidden('#skF_6',B_38)
      | ~ r2_hidden('#skF_7',B_38)
      | ~ v3_ordinal1(B_38)
      | ~ v3_ordinal1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_104787])).

tff(c_104973,plain,(
    ! [B_1231] :
      ( ~ r2_hidden('#skF_6',B_1231)
      | ~ r2_hidden('#skF_7',B_1231)
      | ~ v3_ordinal1(B_1231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_104950])).

tff(c_105406,plain,(
    ! [B_1235] :
      ( ~ r2_hidden('#skF_6',B_1235)
      | ~ v3_ordinal1(B_1235) ) ),
    inference(resolution,[status(thm)],[c_102931,c_104973])).

tff(c_105611,plain,
    ( ~ v3_ordinal1('#skF_1'('#skF_6'))
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_105406])).

tff(c_105720,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_105611])).

tff(c_105723,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_105720])).

tff(c_105727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_105723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.07/13.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.13/13.62  
% 24.13/13.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.20/13.62  %$ r4_wellord1 > r2_hidden > r1_tarski > v4_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 24.20/13.62  
% 24.20/13.62  %Foreground sorts:
% 24.20/13.62  
% 24.20/13.62  
% 24.20/13.62  %Background operators:
% 24.20/13.62  
% 24.20/13.62  
% 24.20/13.62  %Foreground operators:
% 24.20/13.62  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 24.20/13.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.20/13.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.20/13.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 24.20/13.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 24.20/13.62  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 24.20/13.62  tff('#skF_7', type, '#skF_7': $i).
% 24.20/13.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.20/13.62  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 24.20/13.62  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 24.20/13.62  tff('#skF_6', type, '#skF_6': $i).
% 24.20/13.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 24.20/13.62  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 24.20/13.62  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 24.20/13.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.20/13.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 24.20/13.62  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 24.20/13.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 24.20/13.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.20/13.62  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 24.20/13.62  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 24.20/13.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 24.20/13.62  
% 24.20/13.66  tff(f_133, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 24.20/13.66  tff(f_57, axiom, (![A]: (v3_ordinal1(A) => (?[B]: ((v3_ordinal1(B) & r2_hidden(A, B)) & v4_ordinal1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_ordinal1)).
% 24.20/13.66  tff(f_119, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 24.20/13.66  tff(f_48, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 24.20/13.66  tff(f_106, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 24.20/13.66  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 24.20/13.66  tff(f_123, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 24.20/13.66  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 24.20/13.66  tff(f_115, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 24.20/13.66  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 24.20/13.66  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 24.20/13.66  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 24.20/13.66  tff(c_68, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 24.20/13.66  tff(c_12, plain, (![A_7]: (v3_ordinal1('#skF_1'(A_7)) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 24.20/13.66  tff(c_10, plain, (![A_7]: (r2_hidden(A_7, '#skF_1'(A_7)) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 24.20/13.66  tff(c_66, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 24.20/13.66  tff(c_58, plain, (![A_39]: (v2_wellord1(k1_wellord2(A_39)) | ~v3_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_119])).
% 24.20/13.66  tff(c_62, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_133])).
% 24.20/13.66  tff(c_6, plain, (![B_6, A_4]: (r2_hidden(B_6, A_4) | B_6=A_4 | r2_hidden(A_4, B_6) | ~v3_ordinal1(B_6) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 24.20/13.66  tff(c_54, plain, (![A_35]: (v1_relat_1(k1_wellord2(A_35)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 24.20/13.66  tff(c_64, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 24.20/13.66  tff(c_99, plain, (![B_53, A_54]: (r4_wellord1(B_53, A_54) | ~r4_wellord1(A_54, B_53) | ~v1_relat_1(B_53) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_79])).
% 24.20/13.66  tff(c_101, plain, (r4_wellord1(k1_wellord2('#skF_7'), k1_wellord2('#skF_6')) | ~v1_relat_1(k1_wellord2('#skF_7')) | ~v1_relat_1(k1_wellord2('#skF_6'))), inference(resolution, [status(thm)], [c_64, c_99])).
% 24.20/13.66  tff(c_104, plain, (r4_wellord1(k1_wellord2('#skF_7'), k1_wellord2('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_101])).
% 24.20/13.66  tff(c_60, plain, (![B_41, A_40]: (k2_wellord1(k1_wellord2(B_41), A_40)=k1_wellord2(A_40) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_123])).
% 24.20/13.66  tff(c_48, plain, (![A_27]: (k3_relat_1(k1_wellord2(A_27))=A_27 | ~v1_relat_1(k1_wellord2(A_27)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 24.20/13.66  tff(c_74, plain, (![A_27]: (k3_relat_1(k1_wellord2(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48])).
% 24.20/13.66  tff(c_56, plain, (![B_38, A_36]: (k1_wellord1(k1_wellord2(B_38), A_36)=A_36 | ~r2_hidden(A_36, B_38) | ~v3_ordinal1(B_38) | ~v3_ordinal1(A_36))), inference(cnfTransformation, [status(thm)], [f_115])).
% 24.20/13.66  tff(c_337, plain, (![A_87, B_88]: (~r4_wellord1(A_87, k2_wellord1(A_87, k1_wellord1(A_87, B_88))) | ~r2_hidden(B_88, k3_relat_1(A_87)) | ~v2_wellord1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_89])).
% 24.20/13.66  tff(c_340, plain, (![B_38, A_36]: (~r4_wellord1(k1_wellord2(B_38), k2_wellord1(k1_wellord2(B_38), A_36)) | ~r2_hidden(A_36, k3_relat_1(k1_wellord2(B_38))) | ~v2_wellord1(k1_wellord2(B_38)) | ~v1_relat_1(k1_wellord2(B_38)) | ~r2_hidden(A_36, B_38) | ~v3_ordinal1(B_38) | ~v3_ordinal1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_56, c_337])).
% 24.20/13.66  tff(c_562, plain, (![B_114, A_115]: (~r4_wellord1(k1_wellord2(B_114), k2_wellord1(k1_wellord2(B_114), A_115)) | ~v2_wellord1(k1_wellord2(B_114)) | ~r2_hidden(A_115, B_114) | ~v3_ordinal1(B_114) | ~v3_ordinal1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_340])).
% 24.20/13.66  tff(c_2029, plain, (![B_164, A_165]: (~r4_wellord1(k1_wellord2(B_164), k1_wellord2(A_165)) | ~v2_wellord1(k1_wellord2(B_164)) | ~r2_hidden(A_165, B_164) | ~v3_ordinal1(B_164) | ~v3_ordinal1(A_165) | ~r1_tarski(A_165, B_164))), inference(superposition, [status(thm), theory('equality')], [c_60, c_562])).
% 24.20/13.66  tff(c_2032, plain, (~v2_wellord1(k1_wellord2('#skF_7')) | ~r2_hidden('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6') | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_104, c_2029])).
% 24.20/13.66  tff(c_2038, plain, (~v2_wellord1(k1_wellord2('#skF_7')) | ~r2_hidden('#skF_6', '#skF_7') | ~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2032])).
% 24.20/13.66  tff(c_2097, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_2038])).
% 24.20/13.66  tff(c_344, plain, (![B_41, B_88]: (~r4_wellord1(k1_wellord2(B_41), k1_wellord2(k1_wellord1(k1_wellord2(B_41), B_88))) | ~r2_hidden(B_88, k3_relat_1(k1_wellord2(B_41))) | ~v2_wellord1(k1_wellord2(B_41)) | ~v1_relat_1(k1_wellord2(B_41)) | ~r1_tarski(k1_wellord1(k1_wellord2(B_41), B_88), B_41))), inference(superposition, [status(thm), theory('equality')], [c_60, c_337])).
% 24.20/13.66  tff(c_2260, plain, (![B_178, B_179]: (~r4_wellord1(k1_wellord2(B_178), k1_wellord2(k1_wellord1(k1_wellord2(B_178), B_179))) | ~r2_hidden(B_179, B_178) | ~v2_wellord1(k1_wellord2(B_178)) | ~r1_tarski(k1_wellord1(k1_wellord2(B_178), B_179), B_178))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_344])).
% 24.20/13.66  tff(c_41960, plain, (![B_614, A_615]: (~r4_wellord1(k1_wellord2(B_614), k1_wellord2(A_615)) | ~r2_hidden(A_615, B_614) | ~v2_wellord1(k1_wellord2(B_614)) | ~r1_tarski(k1_wellord1(k1_wellord2(B_614), A_615), B_614) | ~r2_hidden(A_615, B_614) | ~v3_ordinal1(B_614) | ~v3_ordinal1(A_615))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2260])).
% 24.20/13.66  tff(c_41962, plain, (~v2_wellord1(k1_wellord2('#skF_7')) | ~r1_tarski(k1_wellord1(k1_wellord2('#skF_7'), '#skF_6'), '#skF_7') | ~r2_hidden('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_104, c_41960])).
% 24.20/13.66  tff(c_41967, plain, (~v2_wellord1(k1_wellord2('#skF_7')) | ~r1_tarski(k1_wellord1(k1_wellord2('#skF_7'), '#skF_6'), '#skF_7') | ~r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_41962])).
% 24.20/13.66  tff(c_41971, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_41967])).
% 24.20/13.66  tff(c_2035, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_7', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_7') | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_2029])).
% 24.20/13.66  tff(c_2041, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_7', '#skF_6') | ~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_2035])).
% 24.20/13.66  tff(c_2098, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_2041])).
% 24.20/13.66  tff(c_41964, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r1_tarski(k1_wellord1(k1_wellord2('#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_7', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_41960])).
% 24.20/13.66  tff(c_41970, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r1_tarski(k1_wellord1(k1_wellord2('#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_41964])).
% 24.20/13.66  tff(c_41984, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_41970])).
% 24.20/13.66  tff(c_41999, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_6, c_41984])).
% 24.20/13.66  tff(c_42020, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_41999])).
% 24.20/13.66  tff(c_42022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41971, c_62, c_42020])).
% 24.20/13.66  tff(c_42024, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_41970])).
% 24.20/13.66  tff(c_206, plain, (![B_72, A_73]: (k1_wellord1(k1_wellord2(B_72), A_73)=A_73 | ~r2_hidden(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(cnfTransformation, [status(thm)], [f_115])).
% 24.20/13.66  tff(c_122, plain, (![D_61, B_62, A_63]: (r2_hidden(k4_tarski(D_61, B_62), A_63) | ~r2_hidden(D_61, k1_wellord1(A_63, B_62)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.20/13.66  tff(c_4, plain, (![A_1, C_3, B_2]: (r2_hidden(A_1, k3_relat_1(C_3)) | ~r2_hidden(k4_tarski(A_1, B_2), C_3) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.20/13.66  tff(c_133, plain, (![D_61, A_63, B_62]: (r2_hidden(D_61, k3_relat_1(A_63)) | ~r2_hidden(D_61, k1_wellord1(A_63, B_62)) | ~v1_relat_1(A_63))), inference(resolution, [status(thm)], [c_122, c_4])).
% 24.20/13.66  tff(c_214, plain, (![D_61, B_72, A_73]: (r2_hidden(D_61, k3_relat_1(k1_wellord2(B_72))) | ~r2_hidden(D_61, A_73) | ~v1_relat_1(k1_wellord2(B_72)) | ~r2_hidden(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_206, c_133])).
% 24.20/13.66  tff(c_258, plain, (![D_78, B_79, A_80]: (r2_hidden(D_78, B_79) | ~r2_hidden(D_78, A_80) | ~r2_hidden(A_80, B_79) | ~v3_ordinal1(B_79) | ~v3_ordinal1(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_214])).
% 24.20/13.66  tff(c_274, plain, (![A_4, B_79, B_6]: (r2_hidden(A_4, B_79) | ~r2_hidden(B_6, B_79) | ~v3_ordinal1(B_79) | r2_hidden(B_6, A_4) | B_6=A_4 | ~v3_ordinal1(B_6) | ~v3_ordinal1(A_4))), inference(resolution, [status(thm)], [c_6, c_258])).
% 24.20/13.66  tff(c_42043, plain, (![A_4]: (r2_hidden(A_4, '#skF_6') | ~v3_ordinal1('#skF_6') | r2_hidden('#skF_7', A_4) | A_4='#skF_7' | ~v3_ordinal1('#skF_7') | ~v3_ordinal1(A_4))), inference(resolution, [status(thm)], [c_42024, c_274])).
% 24.20/13.66  tff(c_42878, plain, (![A_623]: (r2_hidden(A_623, '#skF_6') | r2_hidden('#skF_7', A_623) | A_623='#skF_7' | ~v3_ordinal1(A_623))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_42043])).
% 24.20/13.66  tff(c_566, plain, (![A_116, B_117, C_118]: (r2_hidden(k4_tarski('#skF_2'(A_116, B_117, C_118), B_117), A_116) | r2_hidden('#skF_3'(A_116, B_117, C_118), C_118) | k1_wellord1(A_116, B_117)=C_118 | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.20/13.66  tff(c_2, plain, (![B_2, C_3, A_1]: (r2_hidden(B_2, k3_relat_1(C_3)) | ~r2_hidden(k4_tarski(A_1, B_2), C_3) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.20/13.66  tff(c_620, plain, (![B_119, A_120, C_121]: (r2_hidden(B_119, k3_relat_1(A_120)) | r2_hidden('#skF_3'(A_120, B_119, C_121), C_121) | k1_wellord1(A_120, B_119)=C_121 | ~v1_relat_1(A_120))), inference(resolution, [status(thm)], [c_566, c_2])).
% 24.20/13.66  tff(c_134, plain, (![B_62, A_63, D_61]: (r2_hidden(B_62, k3_relat_1(A_63)) | ~r2_hidden(D_61, k1_wellord1(A_63, B_62)) | ~v1_relat_1(A_63))), inference(resolution, [status(thm)], [c_122, c_2])).
% 24.20/13.66  tff(c_636, plain, (![B_62, A_63, B_119, A_120]: (r2_hidden(B_62, k3_relat_1(A_63)) | ~v1_relat_1(A_63) | r2_hidden(B_119, k3_relat_1(A_120)) | k1_wellord1(A_63, B_62)=k1_wellord1(A_120, B_119) | ~v1_relat_1(A_120))), inference(resolution, [status(thm)], [c_620, c_134])).
% 24.20/13.66  tff(c_851, plain, (![B_136, A_137, B_138, A_139]: (r2_hidden(B_136, k3_relat_1(A_137)) | ~v1_relat_1(A_137) | r2_hidden(B_138, k3_relat_1(A_139)) | k1_wellord1(A_139, B_138)=k1_wellord1(A_137, B_136) | ~v1_relat_1(A_139))), inference(resolution, [status(thm)], [c_620, c_134])).
% 24.20/13.66  tff(c_1022, plain, (![B_136, A_27, B_138, A_139]: (r2_hidden(B_136, A_27) | ~v1_relat_1(k1_wellord2(A_27)) | r2_hidden(B_138, k3_relat_1(A_139)) | k1_wellord1(k1_wellord2(A_27), B_136)=k1_wellord1(A_139, B_138) | ~v1_relat_1(A_139))), inference(superposition, [status(thm), theory('equality')], [c_74, c_851])).
% 24.20/13.66  tff(c_1094, plain, (![B_143, A_144, B_145, A_146]: (r2_hidden(B_143, A_144) | r2_hidden(B_145, k3_relat_1(A_146)) | k1_wellord1(k1_wellord2(A_144), B_143)=k1_wellord1(A_146, B_145) | ~v1_relat_1(A_146))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1022])).
% 24.20/13.66  tff(c_1254, plain, (![B_143, A_144, B_145, A_27]: (r2_hidden(B_143, A_144) | r2_hidden(B_145, A_27) | k1_wellord1(k1_wellord2(A_27), B_145)=k1_wellord1(k1_wellord2(A_144), B_143) | ~v1_relat_1(k1_wellord2(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_1094])).
% 24.20/13.66  tff(c_1303, plain, (![B_147, A_148, B_149, A_150]: (r2_hidden(B_147, A_148) | r2_hidden(B_149, A_150) | k1_wellord1(k1_wellord2(A_150), B_149)=k1_wellord1(k1_wellord2(A_148), B_147))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1254])).
% 24.20/13.66  tff(c_16, plain, (![D_20, B_16, A_9]: (r2_hidden(k4_tarski(D_20, B_16), A_9) | ~r2_hidden(D_20, k1_wellord1(A_9, B_16)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.20/13.66  tff(c_142, plain, (![B_67, A_68, D_69]: (r2_hidden(B_67, k3_relat_1(A_68)) | ~r2_hidden(D_69, k1_wellord1(A_68, B_67)) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_122, c_2])).
% 24.20/13.66  tff(c_146, plain, (![B_67, A_68, D_20, B_16]: (r2_hidden(B_67, k3_relat_1(A_68)) | ~v1_relat_1(A_68) | ~r2_hidden(D_20, k1_wellord1(k1_wellord1(A_68, B_67), B_16)) | ~v1_relat_1(k1_wellord1(A_68, B_67)))), inference(resolution, [status(thm)], [c_16, c_142])).
% 24.20/13.66  tff(c_1345, plain, (![B_16, B_147, D_20, B_149, A_150, A_148]: (r2_hidden(B_149, k3_relat_1(k1_wellord2(A_150))) | ~v1_relat_1(k1_wellord2(A_150)) | ~r2_hidden(D_20, k1_wellord1(k1_wellord1(k1_wellord2(A_148), B_147), B_16)) | ~v1_relat_1(k1_wellord1(k1_wellord2(A_150), B_149)) | r2_hidden(B_147, A_148) | r2_hidden(B_149, A_150))), inference(superposition, [status(thm), theory('equality')], [c_1303, c_146])).
% 24.20/13.66  tff(c_1457, plain, (![B_16, B_147, D_20, B_149, A_150, A_148]: (~r2_hidden(D_20, k1_wellord1(k1_wellord1(k1_wellord2(A_148), B_147), B_16)) | ~v1_relat_1(k1_wellord1(k1_wellord2(A_150), B_149)) | r2_hidden(B_147, A_148) | r2_hidden(B_149, A_150))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_1345])).
% 24.20/13.66  tff(c_4887, plain, (![A_242, B_243]: (~v1_relat_1(k1_wellord1(k1_wellord2(A_242), B_243)) | r2_hidden(B_243, A_242))), inference(splitLeft, [status(thm)], [c_1457])).
% 24.20/13.66  tff(c_4916, plain, (![A_63, B_62, B_119, A_242]: (~v1_relat_1(k1_wellord1(A_63, B_62)) | r2_hidden(B_119, A_242) | r2_hidden(B_62, k3_relat_1(A_63)) | ~v1_relat_1(A_63) | r2_hidden(B_119, k3_relat_1(k1_wellord2(A_242))) | ~v1_relat_1(k1_wellord2(A_242)))), inference(superposition, [status(thm), theory('equality')], [c_636, c_4887])).
% 24.20/13.66  tff(c_4927, plain, (![A_63, B_62, B_119, A_242]: (~v1_relat_1(k1_wellord1(A_63, B_62)) | r2_hidden(B_62, k3_relat_1(A_63)) | ~v1_relat_1(A_63) | r2_hidden(B_119, A_242))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_4916])).
% 24.20/13.66  tff(c_5045, plain, (![B_119, A_242]: (r2_hidden(B_119, A_242))), inference(splitLeft, [status(thm)], [c_4927])).
% 24.20/13.66  tff(c_18, plain, (![D_20, A_9]: (~r2_hidden(D_20, k1_wellord1(A_9, D_20)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.20/13.66  tff(c_5148, plain, (![A_9]: (~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_5045, c_18])).
% 24.20/13.66  tff(c_5152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5148, c_54])).
% 24.20/13.66  tff(c_5154, plain, (![A_249, B_250]: (~v1_relat_1(k1_wellord1(A_249, B_250)) | r2_hidden(B_250, k3_relat_1(A_249)) | ~v1_relat_1(A_249))), inference(splitRight, [status(thm)], [c_4927])).
% 24.20/13.66  tff(c_225, plain, (![D_61, B_72, A_73]: (r2_hidden(D_61, B_72) | ~r2_hidden(D_61, A_73) | ~r2_hidden(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_214])).
% 24.20/13.66  tff(c_6881, plain, (![B_295, B_296, A_297]: (r2_hidden(B_295, B_296) | ~r2_hidden(k3_relat_1(A_297), B_296) | ~v3_ordinal1(B_296) | ~v3_ordinal1(k3_relat_1(A_297)) | ~v1_relat_1(k1_wellord1(A_297, B_295)) | ~v1_relat_1(A_297))), inference(resolution, [status(thm)], [c_5154, c_225])).
% 24.20/13.66  tff(c_6955, plain, (![B_295, B_296, A_27]: (r2_hidden(B_295, B_296) | ~r2_hidden(A_27, B_296) | ~v3_ordinal1(B_296) | ~v3_ordinal1(k3_relat_1(k1_wellord2(A_27))) | ~v1_relat_1(k1_wellord1(k1_wellord2(A_27), B_295)) | ~v1_relat_1(k1_wellord2(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_6881])).
% 24.20/13.66  tff(c_6982, plain, (![B_298, B_299, A_300]: (r2_hidden(B_298, B_299) | ~r2_hidden(A_300, B_299) | ~v3_ordinal1(B_299) | ~v3_ordinal1(A_300) | ~v1_relat_1(k1_wellord1(k1_wellord2(A_300), B_298)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_6955])).
% 24.20/13.66  tff(c_7109, plain, (![B_301, A_302]: (r2_hidden(B_301, '#skF_1'(A_302)) | ~v3_ordinal1('#skF_1'(A_302)) | ~v1_relat_1(k1_wellord1(k1_wellord2(A_302), B_301)) | ~v3_ordinal1(A_302))), inference(resolution, [status(thm)], [c_10, c_6982])).
% 24.20/13.66  tff(c_7447, plain, (![A_311, B_312]: (r2_hidden(A_311, '#skF_1'(B_312)) | ~v3_ordinal1('#skF_1'(B_312)) | ~v1_relat_1(A_311) | ~v3_ordinal1(B_312) | ~r2_hidden(A_311, B_312) | ~v3_ordinal1(B_312) | ~v3_ordinal1(A_311))), inference(superposition, [status(thm), theory('equality')], [c_56, c_7109])).
% 24.20/13.66  tff(c_217, plain, (![A_73, B_72]: (~r2_hidden(A_73, A_73) | ~v1_relat_1(k1_wellord2(B_72)) | ~r2_hidden(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_206, c_18])).
% 24.20/13.66  tff(c_227, plain, (![A_73, B_72]: (~r2_hidden(A_73, A_73) | ~r2_hidden(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_217])).
% 24.20/13.66  tff(c_5315, plain, (![A_257, B_258]: (~r2_hidden(k3_relat_1(A_257), B_258) | ~v3_ordinal1(B_258) | ~v3_ordinal1(k3_relat_1(A_257)) | ~v1_relat_1(k1_wellord1(A_257, k3_relat_1(A_257))) | ~v1_relat_1(A_257))), inference(resolution, [status(thm)], [c_5154, c_227])).
% 24.20/13.66  tff(c_5573, plain, (![A_262]: (~v3_ordinal1('#skF_1'(k3_relat_1(A_262))) | ~v1_relat_1(k1_wellord1(A_262, k3_relat_1(A_262))) | ~v1_relat_1(A_262) | ~v3_ordinal1(k3_relat_1(A_262)))), inference(resolution, [status(thm)], [c_10, c_5315])).
% 24.20/13.66  tff(c_5582, plain, (![A_263]: (~v1_relat_1(k1_wellord1(A_263, k3_relat_1(A_263))) | ~v1_relat_1(A_263) | ~v3_ordinal1(k3_relat_1(A_263)))), inference(resolution, [status(thm)], [c_12, c_5573])).
% 24.20/13.66  tff(c_5626, plain, (![B_38]: (~v1_relat_1(k3_relat_1(k1_wellord2(B_38))) | ~v1_relat_1(k1_wellord2(B_38)) | ~v3_ordinal1(k3_relat_1(k1_wellord2(B_38))) | ~r2_hidden(k3_relat_1(k1_wellord2(B_38)), B_38) | ~v3_ordinal1(B_38) | ~v3_ordinal1(k3_relat_1(k1_wellord2(B_38))))), inference(superposition, [status(thm), theory('equality')], [c_56, c_5582])).
% 24.20/13.66  tff(c_5645, plain, (![B_38]: (~v1_relat_1(B_38) | ~r2_hidden(B_38, B_38) | ~v3_ordinal1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_74, c_54, c_74, c_5626])).
% 24.20/13.66  tff(c_7503, plain, (![B_312]: (~v1_relat_1('#skF_1'(B_312)) | ~r2_hidden('#skF_1'(B_312), B_312) | ~v3_ordinal1(B_312) | ~v3_ordinal1('#skF_1'(B_312)))), inference(resolution, [status(thm)], [c_7447, c_5645])).
% 24.20/13.66  tff(c_42925, plain, (~v1_relat_1('#skF_1'('#skF_6')) | ~v3_ordinal1('#skF_6') | r2_hidden('#skF_7', '#skF_1'('#skF_6')) | '#skF_1'('#skF_6')='#skF_7' | ~v3_ordinal1('#skF_1'('#skF_6'))), inference(resolution, [status(thm)], [c_42878, c_7503])).
% 24.20/13.66  tff(c_43076, plain, (~v1_relat_1('#skF_1'('#skF_6')) | r2_hidden('#skF_7', '#skF_1'('#skF_6')) | '#skF_1'('#skF_6')='#skF_7' | ~v3_ordinal1('#skF_1'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_42925])).
% 24.20/13.66  tff(c_44677, plain, (~v3_ordinal1('#skF_1'('#skF_6'))), inference(splitLeft, [status(thm)], [c_43076])).
% 24.20/13.66  tff(c_45013, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_12, c_44677])).
% 24.20/13.66  tff(c_45017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_45013])).
% 24.20/13.66  tff(c_45019, plain, (v3_ordinal1('#skF_1'('#skF_6'))), inference(splitRight, [status(thm)], [c_43076])).
% 24.20/13.66  tff(c_42963, plain, (![A_623, B_72]: (r2_hidden(A_623, B_72) | ~r2_hidden('#skF_6', B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1('#skF_6') | r2_hidden('#skF_7', A_623) | A_623='#skF_7' | ~v3_ordinal1(A_623))), inference(resolution, [status(thm)], [c_42878, c_225])).
% 24.20/13.66  tff(c_46121, plain, (![A_651, B_652]: (r2_hidden(A_651, B_652) | ~r2_hidden('#skF_6', B_652) | ~v3_ordinal1(B_652) | r2_hidden('#skF_7', A_651) | A_651='#skF_7' | ~v3_ordinal1(A_651))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_42963])).
% 24.20/13.66  tff(c_46246, plain, (![A_651]: (r2_hidden(A_651, '#skF_1'('#skF_6')) | ~v3_ordinal1('#skF_1'('#skF_6')) | r2_hidden('#skF_7', A_651) | A_651='#skF_7' | ~v3_ordinal1(A_651) | ~v3_ordinal1('#skF_6'))), inference(resolution, [status(thm)], [c_10, c_46121])).
% 24.20/13.66  tff(c_46335, plain, (![A_653]: (r2_hidden(A_653, '#skF_1'('#skF_6')) | r2_hidden('#skF_7', A_653) | A_653='#skF_7' | ~v3_ordinal1(A_653))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_45019, c_46246])).
% 24.20/13.66  tff(c_46436, plain, (![B_72]: (~r2_hidden('#skF_1'('#skF_6'), B_72) | ~v3_ordinal1(B_72) | r2_hidden('#skF_7', '#skF_1'('#skF_6')) | '#skF_1'('#skF_6')='#skF_7' | ~v3_ordinal1('#skF_1'('#skF_6')))), inference(resolution, [status(thm)], [c_46335, c_227])).
% 24.20/13.66  tff(c_46529, plain, (![B_72]: (~r2_hidden('#skF_1'('#skF_6'), B_72) | ~v3_ordinal1(B_72) | r2_hidden('#skF_7', '#skF_1'('#skF_6')) | '#skF_1'('#skF_6')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_45019, c_46436])).
% 24.20/13.66  tff(c_46533, plain, (![B_654]: (~r2_hidden('#skF_1'('#skF_6'), B_654) | ~v3_ordinal1(B_654))), inference(splitLeft, [status(thm)], [c_46529])).
% 24.20/13.66  tff(c_46707, plain, (~v3_ordinal1('#skF_1'('#skF_1'('#skF_6'))) | ~v3_ordinal1('#skF_1'('#skF_6'))), inference(resolution, [status(thm)], [c_10, c_46533])).
% 24.20/13.66  tff(c_46800, plain, (~v3_ordinal1('#skF_1'('#skF_1'('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_45019, c_46707])).
% 24.20/13.66  tff(c_46803, plain, (~v3_ordinal1('#skF_1'('#skF_6'))), inference(resolution, [status(thm)], [c_12, c_46800])).
% 24.20/13.66  tff(c_46807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45019, c_46803])).
% 24.20/13.66  tff(c_46808, plain, ('#skF_1'('#skF_6')='#skF_7' | r2_hidden('#skF_7', '#skF_1'('#skF_6'))), inference(splitRight, [status(thm)], [c_46529])).
% 24.20/13.66  tff(c_46809, plain, (r2_hidden('#skF_7', '#skF_1'('#skF_6'))), inference(splitLeft, [status(thm)], [c_46808])).
% 24.20/13.66  tff(c_52, plain, (![C_33, D_34, A_27]: (r1_tarski(C_33, D_34) | ~r2_hidden(k4_tarski(C_33, D_34), k1_wellord2(A_27)) | ~r2_hidden(D_34, A_27) | ~r2_hidden(C_33, A_27) | ~v1_relat_1(k1_wellord2(A_27)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 24.20/13.66  tff(c_362, plain, (![C_92, D_93, A_94]: (r1_tarski(C_92, D_93) | ~r2_hidden(k4_tarski(C_92, D_93), k1_wellord2(A_94)) | ~r2_hidden(D_93, A_94) | ~r2_hidden(C_92, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52])).
% 24.20/13.66  tff(c_372, plain, (![D_20, B_16, A_94]: (r1_tarski(D_20, B_16) | ~r2_hidden(B_16, A_94) | ~r2_hidden(D_20, A_94) | ~r2_hidden(D_20, k1_wellord1(k1_wellord2(A_94), B_16)) | ~v1_relat_1(k1_wellord2(A_94)))), inference(resolution, [status(thm)], [c_16, c_362])).
% 24.20/13.66  tff(c_404, plain, (![D_98, B_99, A_100]: (r1_tarski(D_98, B_99) | ~r2_hidden(B_99, A_100) | ~r2_hidden(D_98, A_100) | ~r2_hidden(D_98, k1_wellord1(k1_wellord2(A_100), B_99)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_372])).
% 24.20/13.66  tff(c_3504, plain, (![D_209, A_210, B_211]: (r1_tarski(D_209, A_210) | ~r2_hidden(A_210, B_211) | ~r2_hidden(D_209, B_211) | ~r2_hidden(D_209, A_210) | ~r2_hidden(A_210, B_211) | ~v3_ordinal1(B_211) | ~v3_ordinal1(A_210))), inference(superposition, [status(thm), theory('equality')], [c_56, c_404])).
% 24.20/13.66  tff(c_3591, plain, (![D_209, A_7]: (r1_tarski(D_209, A_7) | ~r2_hidden(D_209, '#skF_1'(A_7)) | ~r2_hidden(D_209, A_7) | ~r2_hidden(A_7, '#skF_1'(A_7)) | ~v3_ordinal1('#skF_1'(A_7)) | ~v3_ordinal1(A_7))), inference(resolution, [status(thm)], [c_10, c_3504])).
% 24.20/13.66  tff(c_46832, plain, (r1_tarski('#skF_7', '#skF_6') | ~r2_hidden('#skF_7', '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_6')) | ~v3_ordinal1('#skF_1'('#skF_6')) | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_46809, c_3591])).
% 24.20/13.66  tff(c_46873, plain, (r1_tarski('#skF_7', '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_45019, c_42024, c_46832])).
% 24.20/13.66  tff(c_46874, plain, (~r2_hidden('#skF_6', '#skF_1'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_2098, c_46873])).
% 24.20/13.66  tff(c_46997, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_10, c_46874])).
% 24.20/13.66  tff(c_47021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_46997])).
% 24.20/13.66  tff(c_47022, plain, ('#skF_1'('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_46808])).
% 24.20/13.66  tff(c_47126, plain, (r2_hidden('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_47022, c_10])).
% 24.20/13.66  tff(c_47204, plain, (r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_47126])).
% 24.20/13.66  tff(c_47206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41971, c_47204])).
% 24.20/13.66  tff(c_47208, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_41967])).
% 24.20/13.66  tff(c_47229, plain, (![B_72]: (r2_hidden('#skF_6', B_72) | ~r2_hidden('#skF_7', B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1('#skF_7'))), inference(resolution, [status(thm)], [c_47208, c_225])).
% 24.20/13.66  tff(c_47303, plain, (![B_658]: (r2_hidden('#skF_6', B_658) | ~r2_hidden('#skF_7', B_658) | ~v3_ordinal1(B_658))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_47229])).
% 24.20/13.66  tff(c_47465, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_7')) | ~v3_ordinal1('#skF_1'('#skF_7')) | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_10, c_47303])).
% 24.20/13.66  tff(c_47549, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_7')) | ~v3_ordinal1('#skF_1'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_47465])).
% 24.20/13.66  tff(c_47550, plain, (~v3_ordinal1('#skF_1'('#skF_7'))), inference(splitLeft, [status(thm)], [c_47549])).
% 24.20/13.66  tff(c_47553, plain, (~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_12, c_47550])).
% 24.20/13.66  tff(c_47557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_47553])).
% 24.20/13.66  tff(c_47559, plain, (v3_ordinal1('#skF_1'('#skF_7'))), inference(splitRight, [status(thm)], [c_47549])).
% 24.20/13.66  tff(c_47558, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_7'))), inference(splitRight, [status(thm)], [c_47549])).
% 24.20/13.66  tff(c_47898, plain, (r1_tarski('#skF_6', '#skF_7') | ~r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_7', '#skF_1'('#skF_7')) | ~v3_ordinal1('#skF_1'('#skF_7')) | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_47558, c_3591])).
% 24.20/13.66  tff(c_47932, plain, (r1_tarski('#skF_6', '#skF_7') | ~r2_hidden('#skF_7', '#skF_1'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_47559, c_47208, c_47898])).
% 24.20/13.66  tff(c_47933, plain, (~r2_hidden('#skF_7', '#skF_1'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_2097, c_47932])).
% 24.20/13.66  tff(c_47967, plain, (~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_10, c_47933])).
% 24.20/13.66  tff(c_47988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_47967])).
% 24.20/13.66  tff(c_47989, plain, (~r2_hidden('#skF_7', '#skF_6') | ~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitRight, [status(thm)], [c_2041])).
% 24.20/13.66  tff(c_47991, plain, (~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitLeft, [status(thm)], [c_47989])).
% 24.20/13.66  tff(c_47994, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_47991])).
% 24.20/13.66  tff(c_47998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_47994])).
% 24.20/13.66  tff(c_47999, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_47989])).
% 24.20/13.66  tff(c_48003, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_6, c_47999])).
% 24.20/13.66  tff(c_48009, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_48003])).
% 24.20/13.66  tff(c_48010, plain, (r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_62, c_48009])).
% 24.20/13.66  tff(c_48018, plain, (![B_72]: (r2_hidden('#skF_6', B_72) | ~r2_hidden('#skF_7', B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1('#skF_7'))), inference(resolution, [status(thm)], [c_48010, c_225])).
% 24.20/13.66  tff(c_48078, plain, (![B_665]: (r2_hidden('#skF_6', B_665) | ~r2_hidden('#skF_7', B_665) | ~v3_ordinal1(B_665))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_48018])).
% 24.20/13.66  tff(c_48130, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_7')) | ~v3_ordinal1('#skF_1'('#skF_7')) | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_10, c_48078])).
% 24.20/13.66  tff(c_48155, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_7')) | ~v3_ordinal1('#skF_1'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_48130])).
% 24.20/13.66  tff(c_48156, plain, (~v3_ordinal1('#skF_1'('#skF_7'))), inference(splitLeft, [status(thm)], [c_48155])).
% 24.20/13.66  tff(c_48159, plain, (~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_12, c_48156])).
% 24.20/13.66  tff(c_48163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_48159])).
% 24.20/13.66  tff(c_48165, plain, (v3_ordinal1('#skF_1'('#skF_7'))), inference(splitRight, [status(thm)], [c_48155])).
% 24.20/13.66  tff(c_48164, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_7'))), inference(splitRight, [status(thm)], [c_48155])).
% 24.20/13.66  tff(c_48260, plain, (![B_72]: (r2_hidden('#skF_6', B_72) | ~r2_hidden('#skF_1'('#skF_7'), B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1('#skF_1'('#skF_7')))), inference(resolution, [status(thm)], [c_48164, c_225])).
% 24.20/13.66  tff(c_48267, plain, (![B_667]: (r2_hidden('#skF_6', B_667) | ~r2_hidden('#skF_1'('#skF_7'), B_667) | ~v3_ordinal1(B_667))), inference(demodulation, [status(thm), theory('equality')], [c_48165, c_48260])).
% 24.20/13.66  tff(c_48323, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_1'('#skF_7'))) | ~v3_ordinal1('#skF_1'('#skF_1'('#skF_7'))) | ~v3_ordinal1('#skF_1'('#skF_7'))), inference(resolution, [status(thm)], [c_10, c_48267])).
% 24.20/13.66  tff(c_48351, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_1'('#skF_7'))) | ~v3_ordinal1('#skF_1'('#skF_1'('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_48165, c_48323])).
% 24.20/13.66  tff(c_48352, plain, (~v3_ordinal1('#skF_1'('#skF_1'('#skF_7')))), inference(splitLeft, [status(thm)], [c_48351])).
% 24.20/13.66  tff(c_48355, plain, (~v3_ordinal1('#skF_1'('#skF_7'))), inference(resolution, [status(thm)], [c_12, c_48352])).
% 24.20/13.66  tff(c_48359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48165, c_48355])).
% 24.20/13.66  tff(c_48361, plain, (v3_ordinal1('#skF_1'('#skF_1'('#skF_7')))), inference(splitRight, [status(thm)], [c_48351])).
% 24.20/13.66  tff(c_48360, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_1'('#skF_7')))), inference(splitRight, [status(thm)], [c_48351])).
% 24.20/13.66  tff(c_297, plain, (![A_84, B_85]: (r2_hidden(A_84, B_85) | ~r2_hidden('#skF_1'(A_84), B_85) | ~v3_ordinal1(B_85) | ~v3_ordinal1('#skF_1'(A_84)) | ~v3_ordinal1(A_84))), inference(resolution, [status(thm)], [c_10, c_258])).
% 24.20/13.66  tff(c_312, plain, (![A_84]: (r2_hidden(A_84, '#skF_1'('#skF_1'(A_84))) | ~v3_ordinal1('#skF_1'('#skF_1'(A_84))) | ~v3_ordinal1(A_84) | ~v3_ordinal1('#skF_1'(A_84)))), inference(resolution, [status(thm)], [c_10, c_297])).
% 24.20/13.66  tff(c_47990, plain, (r1_tarski('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_2041])).
% 24.20/13.66  tff(c_50, plain, (![C_33, D_34, A_27]: (r2_hidden(k4_tarski(C_33, D_34), k1_wellord2(A_27)) | ~r1_tarski(C_33, D_34) | ~r2_hidden(D_34, A_27) | ~r2_hidden(C_33, A_27) | ~v1_relat_1(k1_wellord2(A_27)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 24.20/13.66  tff(c_378, plain, (![C_95, D_96, A_97]: (r2_hidden(k4_tarski(C_95, D_96), k1_wellord2(A_97)) | ~r1_tarski(C_95, D_96) | ~r2_hidden(D_96, A_97) | ~r2_hidden(C_95, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50])).
% 24.20/13.66  tff(c_14, plain, (![D_20, A_9, B_16]: (r2_hidden(D_20, k1_wellord1(A_9, B_16)) | ~r2_hidden(k4_tarski(D_20, B_16), A_9) | D_20=B_16 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.20/13.66  tff(c_384, plain, (![C_95, A_97, D_96]: (r2_hidden(C_95, k1_wellord1(k1_wellord2(A_97), D_96)) | D_96=C_95 | ~v1_relat_1(k1_wellord2(A_97)) | ~r1_tarski(C_95, D_96) | ~r2_hidden(D_96, A_97) | ~r2_hidden(C_95, A_97))), inference(resolution, [status(thm)], [c_378, c_14])).
% 24.20/13.66  tff(c_396, plain, (![C_95, A_97, D_96]: (r2_hidden(C_95, k1_wellord1(k1_wellord2(A_97), D_96)) | D_96=C_95 | ~r1_tarski(C_95, D_96) | ~r2_hidden(D_96, A_97) | ~r2_hidden(C_95, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_384])).
% 24.20/13.66  tff(c_54298, plain, (![A_740, D_741]: (r2_hidden('#skF_6', k1_wellord1(k1_wellord2(A_740), D_741)) | ~v3_ordinal1(k1_wellord1(k1_wellord2(A_740), D_741)) | D_741='#skF_7' | ~r1_tarski('#skF_7', D_741) | ~r2_hidden(D_741, A_740) | ~r2_hidden('#skF_7', A_740))), inference(resolution, [status(thm)], [c_396, c_48078])).
% 24.20/13.66  tff(c_54325, plain, (![A_740]: (~v1_relat_1(k1_wellord2(A_740)) | ~v3_ordinal1(k1_wellord1(k1_wellord2(A_740), '#skF_6')) | '#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6') | ~r2_hidden('#skF_6', A_740) | ~r2_hidden('#skF_7', A_740))), inference(resolution, [status(thm)], [c_54298, c_18])).
% 24.20/13.66  tff(c_54405, plain, (![A_740]: (~v3_ordinal1(k1_wellord1(k1_wellord2(A_740), '#skF_6')) | '#skF_7'='#skF_6' | ~r2_hidden('#skF_6', A_740) | ~r2_hidden('#skF_7', A_740))), inference(demodulation, [status(thm), theory('equality')], [c_47990, c_54, c_54325])).
% 24.20/13.66  tff(c_54419, plain, (![A_742]: (~v3_ordinal1(k1_wellord1(k1_wellord2(A_742), '#skF_6')) | ~r2_hidden('#skF_6', A_742) | ~r2_hidden('#skF_7', A_742))), inference(negUnitSimplification, [status(thm)], [c_62, c_54405])).
% 24.20/13.66  tff(c_54467, plain, (![B_38]: (~v3_ordinal1('#skF_6') | ~r2_hidden('#skF_6', B_38) | ~r2_hidden('#skF_7', B_38) | ~r2_hidden('#skF_6', B_38) | ~v3_ordinal1(B_38) | ~v3_ordinal1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_54419])).
% 24.20/13.66  tff(c_54478, plain, (![B_743]: (~r2_hidden('#skF_7', B_743) | ~r2_hidden('#skF_6', B_743) | ~v3_ordinal1(B_743))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_54467])).
% 24.20/13.66  tff(c_54598, plain, (~r2_hidden('#skF_6', '#skF_1'('#skF_1'('#skF_7'))) | ~v3_ordinal1('#skF_1'('#skF_1'('#skF_7'))) | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_1'('#skF_7'))), inference(resolution, [status(thm)], [c_312, c_54478])).
% 24.20/13.66  tff(c_54688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48165, c_66, c_48361, c_48360, c_54598])).
% 24.20/13.66  tff(c_54689, plain, (~r2_hidden('#skF_6', '#skF_7') | ~v2_wellord1(k1_wellord2('#skF_7'))), inference(splitRight, [status(thm)], [c_2038])).
% 24.20/13.66  tff(c_54691, plain, (~v2_wellord1(k1_wellord2('#skF_7'))), inference(splitLeft, [status(thm)], [c_54689])).
% 24.20/13.66  tff(c_54694, plain, (~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_54691])).
% 24.20/13.66  tff(c_54698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_54694])).
% 24.20/13.66  tff(c_54699, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_54689])).
% 24.20/13.66  tff(c_55913, plain, (![B_776, B_777]: (~r4_wellord1(k1_wellord2(B_776), k1_wellord2(k1_wellord1(k1_wellord2(B_776), B_777))) | ~r2_hidden(B_777, B_776) | ~v2_wellord1(k1_wellord2(B_776)) | ~r1_tarski(k1_wellord1(k1_wellord2(B_776), B_777), B_776))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_344])).
% 24.20/13.66  tff(c_102788, plain, (![B_1220, A_1221]: (~r4_wellord1(k1_wellord2(B_1220), k1_wellord2(A_1221)) | ~r2_hidden(A_1221, B_1220) | ~v2_wellord1(k1_wellord2(B_1220)) | ~r1_tarski(k1_wellord1(k1_wellord2(B_1220), A_1221), B_1220) | ~r2_hidden(A_1221, B_1220) | ~v3_ordinal1(B_1220) | ~v3_ordinal1(A_1221))), inference(superposition, [status(thm), theory('equality')], [c_56, c_55913])).
% 24.20/13.66  tff(c_102792, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r1_tarski(k1_wellord1(k1_wellord2('#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_7', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_102788])).
% 24.20/13.66  tff(c_102798, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r1_tarski(k1_wellord1(k1_wellord2('#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_102792])).
% 24.20/13.66  tff(c_102799, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_102798])).
% 24.20/13.66  tff(c_102832, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_6, c_102799])).
% 24.20/13.66  tff(c_102875, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_102832])).
% 24.20/13.66  tff(c_102877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54699, c_62, c_102875])).
% 24.20/13.66  tff(c_102879, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_102798])).
% 24.20/13.66  tff(c_102900, plain, (![B_72]: (r2_hidden('#skF_7', B_72) | ~r2_hidden('#skF_6', B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1('#skF_6'))), inference(resolution, [status(thm)], [c_102879, c_225])).
% 24.20/13.66  tff(c_102931, plain, (![B_72]: (r2_hidden('#skF_7', B_72) | ~r2_hidden('#skF_6', B_72) | ~v3_ordinal1(B_72))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102900])).
% 24.20/13.66  tff(c_54690, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_2038])).
% 24.20/13.66  tff(c_102987, plain, (![B_1222]: (r2_hidden('#skF_7', B_1222) | ~r2_hidden('#skF_6', B_1222) | ~v3_ordinal1(B_1222))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102900])).
% 24.20/13.66  tff(c_104484, plain, (![A_1229]: (~v1_relat_1(A_1229) | ~r2_hidden('#skF_6', k1_wellord1(A_1229, '#skF_7')) | ~v3_ordinal1(k1_wellord1(A_1229, '#skF_7')))), inference(resolution, [status(thm)], [c_102987, c_18])).
% 24.20/13.66  tff(c_104685, plain, (![A_97]: (~v1_relat_1(k1_wellord2(A_97)) | ~v3_ordinal1(k1_wellord1(k1_wellord2(A_97), '#skF_7')) | '#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7') | ~r2_hidden('#skF_7', A_97) | ~r2_hidden('#skF_6', A_97))), inference(resolution, [status(thm)], [c_396, c_104484])).
% 24.20/13.66  tff(c_104783, plain, (![A_97]: (~v3_ordinal1(k1_wellord1(k1_wellord2(A_97), '#skF_7')) | '#skF_7'='#skF_6' | ~r2_hidden('#skF_7', A_97) | ~r2_hidden('#skF_6', A_97))), inference(demodulation, [status(thm), theory('equality')], [c_54690, c_54, c_104685])).
% 24.20/13.66  tff(c_104787, plain, (![A_1230]: (~v3_ordinal1(k1_wellord1(k1_wellord2(A_1230), '#skF_7')) | ~r2_hidden('#skF_7', A_1230) | ~r2_hidden('#skF_6', A_1230))), inference(negUnitSimplification, [status(thm)], [c_62, c_104783])).
% 24.20/13.66  tff(c_104950, plain, (![B_38]: (~v3_ordinal1('#skF_7') | ~r2_hidden('#skF_7', B_38) | ~r2_hidden('#skF_6', B_38) | ~r2_hidden('#skF_7', B_38) | ~v3_ordinal1(B_38) | ~v3_ordinal1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_104787])).
% 24.20/13.66  tff(c_104973, plain, (![B_1231]: (~r2_hidden('#skF_6', B_1231) | ~r2_hidden('#skF_7', B_1231) | ~v3_ordinal1(B_1231))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_104950])).
% 24.20/13.66  tff(c_105406, plain, (![B_1235]: (~r2_hidden('#skF_6', B_1235) | ~v3_ordinal1(B_1235))), inference(resolution, [status(thm)], [c_102931, c_104973])).
% 24.20/13.66  tff(c_105611, plain, (~v3_ordinal1('#skF_1'('#skF_6')) | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_10, c_105406])).
% 24.20/13.66  tff(c_105720, plain, (~v3_ordinal1('#skF_1'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_105611])).
% 24.20/13.66  tff(c_105723, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_12, c_105720])).
% 24.20/13.66  tff(c_105727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_105723])).
% 24.20/13.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.20/13.66  
% 24.20/13.66  Inference rules
% 24.20/13.66  ----------------------
% 24.20/13.66  #Ref     : 0
% 24.20/13.66  #Sup     : 24139
% 24.20/13.66  #Fact    : 34
% 24.20/13.66  #Define  : 0
% 24.20/13.66  #Split   : 64
% 24.20/13.66  #Chain   : 0
% 24.20/13.66  #Close   : 0
% 24.20/13.66  
% 24.20/13.66  Ordering : KBO
% 24.20/13.66  
% 24.20/13.66  Simplification rules
% 24.20/13.66  ----------------------
% 24.20/13.66  #Subsume      : 12636
% 24.20/13.66  #Demod        : 17994
% 24.20/13.66  #Tautology    : 1805
% 24.20/13.66  #SimpNegUnit  : 111
% 24.20/13.66  #BackRed      : 318
% 24.20/13.66  
% 24.20/13.66  #Partial instantiations: 0
% 24.20/13.66  #Strategies tried      : 1
% 24.20/13.66  
% 24.20/13.66  Timing (in seconds)
% 24.20/13.66  ----------------------
% 24.20/13.66  Preprocessing        : 0.33
% 24.20/13.66  Parsing              : 0.17
% 24.20/13.66  CNF conversion       : 0.03
% 24.20/13.66  Main loop            : 12.50
% 24.20/13.66  Inferencing          : 2.55
% 24.20/13.66  Reduction            : 2.46
% 24.20/13.66  Demodulation         : 1.64
% 24.20/13.66  BG Simplification    : 0.32
% 24.20/13.66  Subsumption          : 6.45
% 24.20/13.66  Abstraction          : 0.68
% 24.20/13.66  MUC search           : 0.00
% 24.20/13.66  Cooper               : 0.00
% 24.20/13.66  Total                : 12.90
% 24.20/13.66  Index Insertion      : 0.00
% 24.20/13.66  Index Deletion       : 0.00
% 24.20/13.66  Index Matching       : 0.00
% 24.20/13.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
