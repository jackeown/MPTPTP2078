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
% DateTime   : Thu Dec  3 10:05:05 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 145 expanded)
%              Number of leaves         :   30 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  150 ( 406 expanded)
%              Number of equality atoms :   12 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k3_tarski > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_40,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [C_45,A_46,B_47] :
      ( r1_tarski(k9_relat_1(C_45,A_46),k9_relat_1(C_45,B_47))
      | ~ r1_tarski(A_46,B_47)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    ! [A_8] : k3_tarski(k1_zfmisc_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [C_34,B_35,A_36] :
      ( r1_tarski(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(k3_tarski(A_36),B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_95,plain,(
    ! [C_7,B_35,A_3] :
      ( r1_tarski(C_7,B_35)
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_3)),B_35)
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_93])).

tff(c_98,plain,(
    ! [C_37,B_38,A_39] :
      ( r1_tarski(C_37,B_38)
      | ~ r1_tarski(A_39,B_38)
      | ~ r1_tarski(C_37,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_95])).

tff(c_105,plain,(
    ! [C_37] :
      ( r1_tarski(C_37,k9_relat_1('#skF_5','#skF_4'))
      | ~ r1_tarski(C_37,k9_relat_1('#skF_5','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_154,plain,(
    ! [A_46] :
      ( r1_tarski(k9_relat_1('#skF_5',A_46),k9_relat_1('#skF_5','#skF_4'))
      | ~ r1_tarski(A_46,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_148,c_105])).

tff(c_162,plain,(
    ! [A_46] :
      ( r1_tarski(k9_relat_1('#skF_5',A_46),k9_relat_1('#skF_5','#skF_4'))
      | ~ r1_tarski(A_46,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_154])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( k9_relat_1(k2_funct_1(B_22),A_21) = k10_relat_1(B_22,A_21)
      | ~ v2_funct_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k10_relat_1(B_20,k9_relat_1(B_20,A_19)),A_19)
      | ~ v2_funct_1(B_20)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_175,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,k10_relat_1(B_50,k9_relat_1(B_50,A_49)))
      | ~ r1_tarski(A_49,k1_relat_1(B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1896,plain,(
    ! [B_175,A_176] :
      ( k10_relat_1(B_175,k9_relat_1(B_175,A_176)) = A_176
      | ~ r1_tarski(k10_relat_1(B_175,k9_relat_1(B_175,A_176)),A_176)
      | ~ r1_tarski(A_176,k1_relat_1(B_175))
      | ~ v1_relat_1(B_175) ) ),
    inference(resolution,[status(thm)],[c_175,c_2])).

tff(c_1914,plain,(
    ! [B_177,A_178] :
      ( k10_relat_1(B_177,k9_relat_1(B_177,A_178)) = A_178
      | ~ r1_tarski(A_178,k1_relat_1(B_177))
      | ~ v2_funct_1(B_177)
      | ~ v1_funct_1(B_177)
      | ~ v1_relat_1(B_177) ) ),
    inference(resolution,[status(thm)],[c_34,c_1896])).

tff(c_1942,plain,
    ( k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_3')) = '#skF_3'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1914])).

tff(c_1966,plain,(
    k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_1942])).

tff(c_229,plain,(
    ! [B_55,A_56] :
      ( k9_relat_1(k2_funct_1(B_55),A_56) = k10_relat_1(B_55,A_56)
      | ~ v2_funct_1(B_55)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [C_14,A_12,B_13] :
      ( r1_tarski(k9_relat_1(C_14,A_12),k9_relat_1(C_14,B_13))
      | ~ r1_tarski(A_12,B_13)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2486,plain,(
    ! [B_198,A_199,B_200] :
      ( r1_tarski(k10_relat_1(B_198,A_199),k9_relat_1(k2_funct_1(B_198),B_200))
      | ~ r1_tarski(A_199,B_200)
      | ~ v1_relat_1(k2_funct_1(B_198))
      | ~ v2_funct_1(B_198)
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_24])).

tff(c_2521,plain,(
    ! [B_200] :
      ( r1_tarski('#skF_3',k9_relat_1(k2_funct_1('#skF_5'),B_200))
      | ~ r1_tarski(k9_relat_1('#skF_5','#skF_3'),B_200)
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1966,c_2486])).

tff(c_2540,plain,(
    ! [B_200] :
      ( r1_tarski('#skF_3',k9_relat_1(k2_funct_1('#skF_5'),B_200))
      | ~ r1_tarski(k9_relat_1('#skF_5','#skF_3'),B_200)
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_2521])).

tff(c_2541,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2540])).

tff(c_2544,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_2541])).

tff(c_2548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2544])).

tff(c_2626,plain,(
    ! [B_204] :
      ( r1_tarski('#skF_3',k9_relat_1(k2_funct_1('#skF_5'),B_204))
      | ~ r1_tarski(k9_relat_1('#skF_5','#skF_3'),B_204) ) ),
    inference(splitRight,[status(thm)],[c_2540])).

tff(c_2654,plain,(
    ! [A_21] :
      ( r1_tarski('#skF_3',k10_relat_1('#skF_5',A_21))
      | ~ r1_tarski(k9_relat_1('#skF_5','#skF_3'),A_21)
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2626])).

tff(c_2676,plain,(
    ! [A_205] :
      ( r1_tarski('#skF_3',k10_relat_1('#skF_5',A_205))
      | ~ r1_tarski(k9_relat_1('#skF_5','#skF_3'),A_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_2654])).

tff(c_2707,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_4')))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_2676])).

tff(c_2740,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2707])).

tff(c_258,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k10_relat_1(B_61,k9_relat_1(B_61,A_62)),A_62)
      | ~ v2_funct_1(B_61)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_97,plain,(
    ! [C_7,B_35,A_3] :
      ( r1_tarski(C_7,B_35)
      | ~ r1_tarski(A_3,B_35)
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_95])).

tff(c_274,plain,(
    ! [C_7,A_62,B_61] :
      ( r1_tarski(C_7,A_62)
      | ~ r1_tarski(C_7,k10_relat_1(B_61,k9_relat_1(B_61,A_62)))
      | ~ v2_funct_1(B_61)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_258,c_97])).

tff(c_2758,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2740,c_274])).

tff(c_2778,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_2758])).

tff(c_2780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2778])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.11/1.94  
% 5.11/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.11/1.94  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k3_tarski > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.11/1.94  
% 5.11/1.94  %Foreground sorts:
% 5.11/1.94  
% 5.11/1.94  
% 5.11/1.94  %Background operators:
% 5.11/1.94  
% 5.11/1.94  
% 5.11/1.94  %Foreground operators:
% 5.11/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.11/1.94  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.11/1.94  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.11/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.11/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.11/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.11/1.94  tff('#skF_5', type, '#skF_5': $i).
% 5.11/1.94  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.11/1.94  tff('#skF_3', type, '#skF_3': $i).
% 5.11/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.11/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.11/1.94  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.11/1.94  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.11/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.11/1.94  tff('#skF_4', type, '#skF_4': $i).
% 5.11/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.11/1.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.11/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.11/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.11/1.94  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.11/1.94  
% 5.11/1.95  tff(f_103, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 5.11/1.95  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.11/1.95  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 5.11/1.95  tff(f_40, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 5.11/1.95  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.11/1.95  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 5.11/1.95  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 5.11/1.95  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.11/1.95  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 5.11/1.95  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.11/1.95  tff(c_38, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.11/1.95  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.11/1.95  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.11/1.95  tff(c_40, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.11/1.95  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.11/1.95  tff(c_148, plain, (![C_45, A_46, B_47]: (r1_tarski(k9_relat_1(C_45, A_46), k9_relat_1(C_45, B_47)) | ~r1_tarski(A_46, B_47) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.11/1.95  tff(c_44, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.11/1.95  tff(c_20, plain, (![A_8]: (k3_tarski(k1_zfmisc_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.11/1.95  tff(c_10, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.11/1.95  tff(c_93, plain, (![C_34, B_35, A_36]: (r1_tarski(C_34, B_35) | ~r2_hidden(C_34, A_36) | ~r1_tarski(k3_tarski(A_36), B_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.11/1.95  tff(c_95, plain, (![C_7, B_35, A_3]: (r1_tarski(C_7, B_35) | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_3)), B_35) | ~r1_tarski(C_7, A_3))), inference(resolution, [status(thm)], [c_10, c_93])).
% 5.11/1.95  tff(c_98, plain, (![C_37, B_38, A_39]: (r1_tarski(C_37, B_38) | ~r1_tarski(A_39, B_38) | ~r1_tarski(C_37, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_95])).
% 5.11/1.95  tff(c_105, plain, (![C_37]: (r1_tarski(C_37, k9_relat_1('#skF_5', '#skF_4')) | ~r1_tarski(C_37, k9_relat_1('#skF_5', '#skF_3')))), inference(resolution, [status(thm)], [c_44, c_98])).
% 5.11/1.95  tff(c_154, plain, (![A_46]: (r1_tarski(k9_relat_1('#skF_5', A_46), k9_relat_1('#skF_5', '#skF_4')) | ~r1_tarski(A_46, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_148, c_105])).
% 5.11/1.95  tff(c_162, plain, (![A_46]: (r1_tarski(k9_relat_1('#skF_5', A_46), k9_relat_1('#skF_5', '#skF_4')) | ~r1_tarski(A_46, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_154])).
% 5.11/1.95  tff(c_36, plain, (![B_22, A_21]: (k9_relat_1(k2_funct_1(B_22), A_21)=k10_relat_1(B_22, A_21) | ~v2_funct_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.11/1.95  tff(c_30, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.11/1.95  tff(c_42, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.11/1.95  tff(c_34, plain, (![B_20, A_19]: (r1_tarski(k10_relat_1(B_20, k9_relat_1(B_20, A_19)), A_19) | ~v2_funct_1(B_20) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.11/1.95  tff(c_175, plain, (![A_49, B_50]: (r1_tarski(A_49, k10_relat_1(B_50, k9_relat_1(B_50, A_49))) | ~r1_tarski(A_49, k1_relat_1(B_50)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.11/1.95  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.11/1.95  tff(c_1896, plain, (![B_175, A_176]: (k10_relat_1(B_175, k9_relat_1(B_175, A_176))=A_176 | ~r1_tarski(k10_relat_1(B_175, k9_relat_1(B_175, A_176)), A_176) | ~r1_tarski(A_176, k1_relat_1(B_175)) | ~v1_relat_1(B_175))), inference(resolution, [status(thm)], [c_175, c_2])).
% 5.11/1.95  tff(c_1914, plain, (![B_177, A_178]: (k10_relat_1(B_177, k9_relat_1(B_177, A_178))=A_178 | ~r1_tarski(A_178, k1_relat_1(B_177)) | ~v2_funct_1(B_177) | ~v1_funct_1(B_177) | ~v1_relat_1(B_177))), inference(resolution, [status(thm)], [c_34, c_1896])).
% 5.11/1.95  tff(c_1942, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_3'))='#skF_3' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_1914])).
% 5.11/1.95  tff(c_1966, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_1942])).
% 5.11/1.95  tff(c_229, plain, (![B_55, A_56]: (k9_relat_1(k2_funct_1(B_55), A_56)=k10_relat_1(B_55, A_56) | ~v2_funct_1(B_55) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.11/1.95  tff(c_24, plain, (![C_14, A_12, B_13]: (r1_tarski(k9_relat_1(C_14, A_12), k9_relat_1(C_14, B_13)) | ~r1_tarski(A_12, B_13) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.11/1.95  tff(c_2486, plain, (![B_198, A_199, B_200]: (r1_tarski(k10_relat_1(B_198, A_199), k9_relat_1(k2_funct_1(B_198), B_200)) | ~r1_tarski(A_199, B_200) | ~v1_relat_1(k2_funct_1(B_198)) | ~v2_funct_1(B_198) | ~v1_funct_1(B_198) | ~v1_relat_1(B_198))), inference(superposition, [status(thm), theory('equality')], [c_229, c_24])).
% 5.11/1.95  tff(c_2521, plain, (![B_200]: (r1_tarski('#skF_3', k9_relat_1(k2_funct_1('#skF_5'), B_200)) | ~r1_tarski(k9_relat_1('#skF_5', '#skF_3'), B_200) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1966, c_2486])).
% 5.11/1.95  tff(c_2540, plain, (![B_200]: (r1_tarski('#skF_3', k9_relat_1(k2_funct_1('#skF_5'), B_200)) | ~r1_tarski(k9_relat_1('#skF_5', '#skF_3'), B_200) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_2521])).
% 5.11/1.95  tff(c_2541, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_2540])).
% 5.11/1.95  tff(c_2544, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_2541])).
% 5.11/1.95  tff(c_2548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2544])).
% 5.11/1.95  tff(c_2626, plain, (![B_204]: (r1_tarski('#skF_3', k9_relat_1(k2_funct_1('#skF_5'), B_204)) | ~r1_tarski(k9_relat_1('#skF_5', '#skF_3'), B_204))), inference(splitRight, [status(thm)], [c_2540])).
% 5.11/1.95  tff(c_2654, plain, (![A_21]: (r1_tarski('#skF_3', k10_relat_1('#skF_5', A_21)) | ~r1_tarski(k9_relat_1('#skF_5', '#skF_3'), A_21) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2626])).
% 5.11/1.95  tff(c_2676, plain, (![A_205]: (r1_tarski('#skF_3', k10_relat_1('#skF_5', A_205)) | ~r1_tarski(k9_relat_1('#skF_5', '#skF_3'), A_205))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_2654])).
% 5.11/1.95  tff(c_2707, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_4'))) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_162, c_2676])).
% 5.11/1.95  tff(c_2740, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2707])).
% 5.11/1.95  tff(c_258, plain, (![B_61, A_62]: (r1_tarski(k10_relat_1(B_61, k9_relat_1(B_61, A_62)), A_62) | ~v2_funct_1(B_61) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.11/1.95  tff(c_97, plain, (![C_7, B_35, A_3]: (r1_tarski(C_7, B_35) | ~r1_tarski(A_3, B_35) | ~r1_tarski(C_7, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_95])).
% 5.11/1.95  tff(c_274, plain, (![C_7, A_62, B_61]: (r1_tarski(C_7, A_62) | ~r1_tarski(C_7, k10_relat_1(B_61, k9_relat_1(B_61, A_62))) | ~v2_funct_1(B_61) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_258, c_97])).
% 5.11/1.95  tff(c_2758, plain, (r1_tarski('#skF_3', '#skF_4') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2740, c_274])).
% 5.11/1.95  tff(c_2778, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_2758])).
% 5.11/1.95  tff(c_2780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_2778])).
% 5.11/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.11/1.95  
% 5.11/1.95  Inference rules
% 5.11/1.95  ----------------------
% 5.11/1.95  #Ref     : 0
% 5.11/1.95  #Sup     : 687
% 5.11/1.95  #Fact    : 0
% 5.11/1.95  #Define  : 0
% 5.11/1.95  #Split   : 8
% 5.11/1.95  #Chain   : 0
% 5.11/1.95  #Close   : 0
% 5.11/1.95  
% 5.11/1.95  Ordering : KBO
% 5.11/1.95  
% 5.11/1.95  Simplification rules
% 5.11/1.95  ----------------------
% 5.11/1.95  #Subsume      : 159
% 5.11/1.95  #Demod        : 212
% 5.11/1.95  #Tautology    : 58
% 5.11/1.95  #SimpNegUnit  : 1
% 5.11/1.95  #BackRed      : 0
% 5.11/1.95  
% 5.11/1.95  #Partial instantiations: 0
% 5.11/1.95  #Strategies tried      : 1
% 5.11/1.95  
% 5.11/1.95  Timing (in seconds)
% 5.11/1.95  ----------------------
% 5.11/1.96  Preprocessing        : 0.31
% 5.11/1.96  Parsing              : 0.16
% 5.11/1.96  CNF conversion       : 0.02
% 5.11/1.96  Main loop            : 0.85
% 5.11/1.96  Inferencing          : 0.26
% 5.11/1.96  Reduction            : 0.22
% 5.11/1.96  Demodulation         : 0.15
% 5.11/1.96  BG Simplification    : 0.04
% 5.11/1.96  Subsumption          : 0.27
% 5.11/1.96  Abstraction          : 0.05
% 5.11/1.96  MUC search           : 0.00
% 5.11/1.96  Cooper               : 0.00
% 5.11/1.96  Total                : 1.20
% 5.11/1.96  Index Insertion      : 0.00
% 5.11/1.96  Index Deletion       : 0.00
% 5.11/1.96  Index Matching       : 0.00
% 5.11/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
