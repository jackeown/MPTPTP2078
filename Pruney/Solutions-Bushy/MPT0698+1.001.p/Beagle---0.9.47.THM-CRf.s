%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0698+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:43 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 175 expanded)
%              Number of leaves         :   31 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  154 ( 493 expanded)
%              Number of equality atoms :   31 (  77 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k1_funct_1 > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( ! [B] : r1_tarski(k10_relat_1(A,k9_relat_1(A,B)),B)
         => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_98,plain,(
    ! [A_71] :
      ( '#skF_5'(A_71) != '#skF_6'(A_71)
      | v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    ~ v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_101,plain,
    ( '#skF_5'('#skF_7') != '#skF_6'('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_98,c_46])).

tff(c_104,plain,(
    '#skF_5'('#skF_7') != '#skF_6'('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_101])).

tff(c_30,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_5'(A_44),k1_relat_1(A_44))
      | v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,(
    ! [A_66,B_67] :
      ( k9_relat_1(A_66,k1_tarski(B_67)) = k11_relat_1(A_66,B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [B_60] : r1_tarski(k10_relat_1('#skF_7',k9_relat_1('#skF_7',B_60)),B_60) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_69,plain,(
    ! [B_67] :
      ( r1_tarski(k10_relat_1('#skF_7',k11_relat_1('#skF_7',B_67)),k1_tarski(B_67))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_48])).

tff(c_75,plain,(
    ! [B_67] : r1_tarski(k10_relat_1('#skF_7',k11_relat_1('#skF_7',B_67)),k1_tarski(B_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_69])).

tff(c_78,plain,(
    ! [B_69,A_70] :
      ( k1_tarski(B_69) = A_70
      | k1_xboole_0 = A_70
      | ~ r1_tarski(A_70,k1_tarski(B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_92,plain,(
    ! [B_67] :
      ( k10_relat_1('#skF_7',k11_relat_1('#skF_7',B_67)) = k1_tarski(B_67)
      | k10_relat_1('#skF_7',k11_relat_1('#skF_7',B_67)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_75,c_78])).

tff(c_28,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_6'(A_44),k1_relat_1(A_44))
      | v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_247,plain,(
    ! [B_86,A_87] :
      ( k1_tarski(k1_funct_1(B_86,A_87)) = k11_relat_1(B_86,A_87)
      | ~ r2_hidden(A_87,k1_relat_1(B_86))
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_254,plain,(
    ! [A_44] :
      ( k1_tarski(k1_funct_1(A_44,'#skF_6'(A_44))) = k11_relat_1(A_44,'#skF_6'(A_44))
      | v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_28,c_247])).

tff(c_26,plain,(
    ! [A_44] :
      ( k1_funct_1(A_44,'#skF_5'(A_44)) = k1_funct_1(A_44,'#skF_6'(A_44))
      | v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_310,plain,(
    ! [A_94] :
      ( k1_tarski(k1_funct_1(A_94,'#skF_5'(A_94))) = k11_relat_1(A_94,'#skF_5'(A_94))
      | v2_funct_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_30,c_247])).

tff(c_700,plain,(
    ! [A_129] :
      ( k1_tarski(k1_funct_1(A_129,'#skF_6'(A_129))) = k11_relat_1(A_129,'#skF_5'(A_129))
      | v2_funct_1(A_129)
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129)
      | v2_funct_1(A_129)
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_310])).

tff(c_2663,plain,(
    ! [A_257] :
      ( k11_relat_1(A_257,'#skF_5'(A_257)) = k11_relat_1(A_257,'#skF_6'(A_257))
      | v2_funct_1(A_257)
      | ~ v1_funct_1(A_257)
      | ~ v1_relat_1(A_257)
      | v2_funct_1(A_257)
      | ~ v1_funct_1(A_257)
      | ~ v1_relat_1(A_257)
      | v2_funct_1(A_257)
      | ~ v1_funct_1(A_257)
      | ~ v1_relat_1(A_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_700])).

tff(c_2737,plain,
    ( r1_tarski(k10_relat_1('#skF_7',k11_relat_1('#skF_7','#skF_6'('#skF_7'))),k1_tarski('#skF_5'('#skF_7')))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2663,c_75])).

tff(c_2749,plain,
    ( r1_tarski(k10_relat_1('#skF_7',k11_relat_1('#skF_7','#skF_6'('#skF_7'))),k1_tarski('#skF_5'('#skF_7')))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_52,c_50,c_52,c_50,c_2737])).

tff(c_2750,plain,(
    r1_tarski(k10_relat_1('#skF_7',k11_relat_1('#skF_7','#skF_6'('#skF_7'))),k1_tarski('#skF_5'('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2749])).

tff(c_2760,plain,
    ( r1_tarski(k1_tarski('#skF_6'('#skF_7')),k1_tarski('#skF_5'('#skF_7')))
    | k10_relat_1('#skF_7',k11_relat_1('#skF_7','#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2750])).

tff(c_2763,plain,(
    k10_relat_1('#skF_7',k11_relat_1('#skF_7','#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2760])).

tff(c_206,plain,(
    ! [A_83,D_84] :
      ( r2_hidden(k1_funct_1(A_83,D_84),k2_relat_1(A_83))
      | ~ r2_hidden(D_84,k1_relat_1(A_83))
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_873,plain,(
    ! [A_141] :
      ( r2_hidden(k1_funct_1(A_141,'#skF_6'(A_141)),k2_relat_1(A_141))
      | ~ r2_hidden('#skF_5'(A_141),k1_relat_1(A_141))
      | ~ v1_funct_1(A_141)
      | ~ v1_relat_1(A_141)
      | v2_funct_1(A_141)
      | ~ v1_funct_1(A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_206])).

tff(c_36,plain,(
    ! [B_54,A_53] :
      ( k10_relat_1(B_54,k1_tarski(A_53)) != k1_xboole_0
      | ~ r2_hidden(A_53,k2_relat_1(B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_878,plain,(
    ! [A_142] :
      ( k10_relat_1(A_142,k1_tarski(k1_funct_1(A_142,'#skF_6'(A_142)))) != k1_xboole_0
      | ~ r2_hidden('#skF_5'(A_142),k1_relat_1(A_142))
      | v2_funct_1(A_142)
      | ~ v1_funct_1(A_142)
      | ~ v1_relat_1(A_142) ) ),
    inference(resolution,[status(thm)],[c_873,c_36])).

tff(c_884,plain,(
    ! [A_44] :
      ( k10_relat_1(A_44,k11_relat_1(A_44,'#skF_6'(A_44))) != k1_xboole_0
      | ~ r2_hidden('#skF_5'(A_44),k1_relat_1(A_44))
      | v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44)
      | v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_878])).

tff(c_2768,plain,
    ( ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2763,c_884])).

tff(c_2790,plain,
    ( ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7'))
    | v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2768])).

tff(c_2791,plain,(
    ~ r2_hidden('#skF_5'('#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2790])).

tff(c_2804,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_2791])).

tff(c_2807,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2804])).

tff(c_2809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2807])).

tff(c_2810,plain,(
    r1_tarski(k1_tarski('#skF_6'('#skF_7')),k1_tarski('#skF_5'('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_2760])).

tff(c_44,plain,(
    ! [B_58,A_57] :
      ( B_58 = A_57
      | ~ r1_tarski(k1_tarski(A_57),k1_tarski(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2817,plain,(
    '#skF_5'('#skF_7') = '#skF_6'('#skF_7') ),
    inference(resolution,[status(thm)],[c_2810,c_44])).

tff(c_2824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_2817])).

%------------------------------------------------------------------------------
