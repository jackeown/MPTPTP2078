%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:38 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 140 expanded)
%              Number of leaves         :   29 (  68 expanded)
%              Depth                    :   20
%              Number of atoms          :  148 ( 442 expanded)
%              Number of equality atoms :   41 ( 154 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_9 > #skF_7 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = A )
             => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_44,plain,(
    k6_relat_1(k1_relat_1('#skF_10')) != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_50,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_8'(k1_relat_1(B_108),B_108),k1_relat_1(B_108))
      | k6_relat_1(k1_relat_1(B_108)) = B_108
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48,plain,(
    k2_relat_1('#skF_9') = k1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    ! [A_106] :
      ( k9_relat_1(A_106,k1_relat_1(A_106)) = k2_relat_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_hidden(k4_tarski('#skF_7'(A_100,B_101,C_102),A_100),C_102)
      | ~ r2_hidden(A_100,k9_relat_1(C_102,B_101))
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    k5_relat_1('#skF_9','#skF_10') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_218,plain,(
    ! [D_161,B_162,A_163,E_164] :
      ( r2_hidden(k4_tarski(D_161,'#skF_1'(B_162,k5_relat_1(A_163,B_162),A_163,D_161,E_164)),A_163)
      | ~ r2_hidden(k4_tarski(D_161,E_164),k5_relat_1(A_163,B_162))
      | ~ v1_relat_1(k5_relat_1(A_163,B_162))
      | ~ v1_relat_1(B_162)
      | ~ v1_relat_1(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_238,plain,(
    ! [D_161,E_164] :
      ( r2_hidden(k4_tarski(D_161,'#skF_1'('#skF_10','#skF_9','#skF_9',D_161,E_164)),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_161,E_164),k5_relat_1('#skF_9','#skF_10'))
      | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_10'))
      | ~ v1_relat_1('#skF_10')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_218])).

tff(c_253,plain,(
    ! [D_167,E_168] :
      ( r2_hidden(k4_tarski(D_167,'#skF_1'('#skF_10','#skF_9','#skF_9',D_167,E_168)),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_167,E_168),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_56,c_46,c_46,c_238])).

tff(c_40,plain,(
    ! [C_114,A_112,B_113] :
      ( k1_funct_1(C_114,A_112) = B_113
      | ~ r2_hidden(k4_tarski(A_112,B_113),C_114)
      | ~ v1_funct_1(C_114)
      | ~ v1_relat_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_263,plain,(
    ! [D_167,E_168] :
      ( k1_funct_1('#skF_9',D_167) = '#skF_1'('#skF_10','#skF_9','#skF_9',D_167,E_168)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(k4_tarski(D_167,E_168),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_253,c_40])).

tff(c_329,plain,(
    ! [D_175,E_176] :
      ( k1_funct_1('#skF_9',D_175) = '#skF_1'('#skF_10','#skF_9','#skF_9',D_175,E_176)
      | ~ r2_hidden(k4_tarski(D_175,E_176),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_263])).

tff(c_348,plain,(
    ! [A_100,B_101] :
      ( k1_funct_1('#skF_9','#skF_7'(A_100,B_101,'#skF_9')) = '#skF_1'('#skF_10','#skF_9','#skF_9','#skF_7'(A_100,B_101,'#skF_9'),A_100)
      | ~ r2_hidden(A_100,k9_relat_1('#skF_9',B_101))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_329])).

tff(c_575,plain,(
    ! [A_189,B_190] :
      ( k1_funct_1('#skF_9','#skF_7'(A_189,B_190,'#skF_9')) = '#skF_1'('#skF_10','#skF_9','#skF_9','#skF_7'(A_189,B_190,'#skF_9'),A_189)
      | ~ r2_hidden(A_189,k9_relat_1('#skF_9',B_190)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_348])).

tff(c_599,plain,(
    ! [A_189] :
      ( k1_funct_1('#skF_9','#skF_7'(A_189,k1_relat_1('#skF_9'),'#skF_9')) = '#skF_1'('#skF_10','#skF_9','#skF_9','#skF_7'(A_189,k1_relat_1('#skF_9'),'#skF_9'),A_189)
      | ~ r2_hidden(A_189,k2_relat_1('#skF_9'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_575])).

tff(c_768,plain,(
    ! [A_200] :
      ( k1_funct_1('#skF_9','#skF_7'(A_200,k1_relat_1('#skF_9'),'#skF_9')) = '#skF_1'('#skF_10','#skF_9','#skF_9','#skF_7'(A_200,k1_relat_1('#skF_9'),'#skF_9'),A_200)
      | ~ r2_hidden(A_200,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_599])).

tff(c_80,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden(k4_tarski('#skF_7'(A_132,B_133,C_134),A_132),C_134)
      | ~ r2_hidden(A_132,k9_relat_1(C_134,B_133))
      | ~ v1_relat_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_100,plain,(
    ! [C_138,A_139,B_140] :
      ( k1_funct_1(C_138,'#skF_7'(A_139,B_140,C_138)) = A_139
      | ~ v1_funct_1(C_138)
      | ~ r2_hidden(A_139,k9_relat_1(C_138,B_140))
      | ~ v1_relat_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_80,c_40])).

tff(c_111,plain,(
    ! [A_106,A_139] :
      ( k1_funct_1(A_106,'#skF_7'(A_139,k1_relat_1(A_106),A_106)) = A_139
      | ~ v1_funct_1(A_106)
      | ~ r2_hidden(A_139,k2_relat_1(A_106))
      | ~ v1_relat_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_100])).

tff(c_801,plain,(
    ! [A_200] :
      ( '#skF_1'('#skF_10','#skF_9','#skF_9','#skF_7'(A_200,k1_relat_1('#skF_9'),'#skF_9'),A_200) = A_200
      | ~ v1_funct_1('#skF_9')
      | ~ r2_hidden(A_200,k2_relat_1('#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(A_200,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_111])).

tff(c_825,plain,(
    ! [A_201] :
      ( '#skF_1'('#skF_10','#skF_9','#skF_9','#skF_7'(A_201,k1_relat_1('#skF_9'),'#skF_9'),A_201) = A_201
      | ~ r2_hidden(A_201,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_48,c_54,c_801])).

tff(c_151,plain,(
    ! [B_153,A_154,D_155,E_156] :
      ( r2_hidden(k4_tarski('#skF_1'(B_153,k5_relat_1(A_154,B_153),A_154,D_155,E_156),E_156),B_153)
      | ~ r2_hidden(k4_tarski(D_155,E_156),k5_relat_1(A_154,B_153))
      | ~ v1_relat_1(k5_relat_1(A_154,B_153))
      | ~ v1_relat_1(B_153)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_167,plain,(
    ! [D_155,E_156] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9','#skF_9',D_155,E_156),E_156),'#skF_10')
      | ~ r2_hidden(k4_tarski(D_155,E_156),k5_relat_1('#skF_9','#skF_10'))
      | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_10'))
      | ~ v1_relat_1('#skF_10')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_151])).

tff(c_175,plain,(
    ! [D_157,E_158] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_10','#skF_9','#skF_9',D_157,E_158),E_158),'#skF_10')
      | ~ r2_hidden(k4_tarski(D_157,E_158),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_56,c_46,c_46,c_167])).

tff(c_182,plain,(
    ! [D_157,E_158] :
      ( k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9','#skF_9',D_157,E_158)) = E_158
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(k4_tarski(D_157,E_158),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_175,c_40])).

tff(c_196,plain,(
    ! [D_159,E_160] :
      ( k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9','#skF_9',D_159,E_160)) = E_160
      | ~ r2_hidden(k4_tarski(D_159,E_160),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_182])).

tff(c_208,plain,(
    ! [A_100,B_101] :
      ( k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9','#skF_9','#skF_7'(A_100,B_101,'#skF_9'),A_100)) = A_100
      | ~ r2_hidden(A_100,k9_relat_1('#skF_9',B_101))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_196])).

tff(c_217,plain,(
    ! [A_100,B_101] :
      ( k1_funct_1('#skF_10','#skF_1'('#skF_10','#skF_9','#skF_9','#skF_7'(A_100,B_101,'#skF_9'),A_100)) = A_100
      | ~ r2_hidden(A_100,k9_relat_1('#skF_9',B_101)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_208])).

tff(c_975,plain,(
    ! [A_205] :
      ( k1_funct_1('#skF_10',A_205) = A_205
      | ~ r2_hidden(A_205,k9_relat_1('#skF_9',k1_relat_1('#skF_9')))
      | ~ r2_hidden(A_205,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_217])).

tff(c_1014,plain,(
    ! [A_205] :
      ( k1_funct_1('#skF_10',A_205) = A_205
      | ~ r2_hidden(A_205,k2_relat_1('#skF_9'))
      | ~ r2_hidden(A_205,k1_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_975])).

tff(c_1026,plain,(
    ! [A_206] :
      ( k1_funct_1('#skF_10',A_206) = A_206
      | ~ r2_hidden(A_206,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_1014])).

tff(c_1057,plain,
    ( k1_funct_1('#skF_10','#skF_8'(k1_relat_1('#skF_10'),'#skF_10')) = '#skF_8'(k1_relat_1('#skF_10'),'#skF_10')
    | k6_relat_1(k1_relat_1('#skF_10')) = '#skF_10'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_32,c_1026])).

tff(c_1083,plain,
    ( k1_funct_1('#skF_10','#skF_8'(k1_relat_1('#skF_10'),'#skF_10')) = '#skF_8'(k1_relat_1('#skF_10'),'#skF_10')
    | k6_relat_1(k1_relat_1('#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1057])).

tff(c_1084,plain,(
    k1_funct_1('#skF_10','#skF_8'(k1_relat_1('#skF_10'),'#skF_10')) = '#skF_8'(k1_relat_1('#skF_10'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1083])).

tff(c_30,plain,(
    ! [B_108] :
      ( k1_funct_1(B_108,'#skF_8'(k1_relat_1(B_108),B_108)) != '#skF_8'(k1_relat_1(B_108),B_108)
      | k6_relat_1(k1_relat_1(B_108)) = B_108
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1094,plain,
    ( k6_relat_1(k1_relat_1('#skF_10')) = '#skF_10'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1084,c_30])).

tff(c_1102,plain,(
    k6_relat_1(k1_relat_1('#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1094])).

tff(c_1104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:14:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.57  
% 3.48/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.57  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_9 > #skF_7 > #skF_1 > #skF_3
% 3.48/1.57  
% 3.48/1.57  %Foreground sorts:
% 3.48/1.57  
% 3.48/1.57  
% 3.48/1.57  %Background operators:
% 3.48/1.57  
% 3.48/1.57  
% 3.48/1.57  %Foreground operators:
% 3.48/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.57  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.48/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.48/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.48/1.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.48/1.57  tff('#skF_10', type, '#skF_10': $i).
% 3.48/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.48/1.57  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.48/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.48/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.48/1.57  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.48/1.57  tff('#skF_9', type, '#skF_9': $i).
% 3.48/1.57  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.48/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.48/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.48/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.48/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.48/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.48/1.57  
% 3.48/1.59  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 3.48/1.59  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 3.48/1.59  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.48/1.59  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.48/1.59  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 3.48/1.59  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.48/1.59  tff(c_44, plain, (k6_relat_1(k1_relat_1('#skF_10'))!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.48/1.59  tff(c_52, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.48/1.59  tff(c_50, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.48/1.59  tff(c_32, plain, (![B_108]: (r2_hidden('#skF_8'(k1_relat_1(B_108), B_108), k1_relat_1(B_108)) | k6_relat_1(k1_relat_1(B_108))=B_108 | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.48/1.59  tff(c_56, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.48/1.59  tff(c_48, plain, (k2_relat_1('#skF_9')=k1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.48/1.59  tff(c_28, plain, (![A_106]: (k9_relat_1(A_106, k1_relat_1(A_106))=k2_relat_1(A_106) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.59  tff(c_54, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.48/1.59  tff(c_24, plain, (![A_100, B_101, C_102]: (r2_hidden(k4_tarski('#skF_7'(A_100, B_101, C_102), A_100), C_102) | ~r2_hidden(A_100, k9_relat_1(C_102, B_101)) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.48/1.59  tff(c_46, plain, (k5_relat_1('#skF_9', '#skF_10')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.48/1.59  tff(c_218, plain, (![D_161, B_162, A_163, E_164]: (r2_hidden(k4_tarski(D_161, '#skF_1'(B_162, k5_relat_1(A_163, B_162), A_163, D_161, E_164)), A_163) | ~r2_hidden(k4_tarski(D_161, E_164), k5_relat_1(A_163, B_162)) | ~v1_relat_1(k5_relat_1(A_163, B_162)) | ~v1_relat_1(B_162) | ~v1_relat_1(A_163))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.59  tff(c_238, plain, (![D_161, E_164]: (r2_hidden(k4_tarski(D_161, '#skF_1'('#skF_10', '#skF_9', '#skF_9', D_161, E_164)), '#skF_9') | ~r2_hidden(k4_tarski(D_161, E_164), k5_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_218])).
% 3.48/1.59  tff(c_253, plain, (![D_167, E_168]: (r2_hidden(k4_tarski(D_167, '#skF_1'('#skF_10', '#skF_9', '#skF_9', D_167, E_168)), '#skF_9') | ~r2_hidden(k4_tarski(D_167, E_168), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_56, c_46, c_46, c_238])).
% 3.48/1.59  tff(c_40, plain, (![C_114, A_112, B_113]: (k1_funct_1(C_114, A_112)=B_113 | ~r2_hidden(k4_tarski(A_112, B_113), C_114) | ~v1_funct_1(C_114) | ~v1_relat_1(C_114))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.48/1.59  tff(c_263, plain, (![D_167, E_168]: (k1_funct_1('#skF_9', D_167)='#skF_1'('#skF_10', '#skF_9', '#skF_9', D_167, E_168) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(k4_tarski(D_167, E_168), '#skF_9'))), inference(resolution, [status(thm)], [c_253, c_40])).
% 3.48/1.59  tff(c_329, plain, (![D_175, E_176]: (k1_funct_1('#skF_9', D_175)='#skF_1'('#skF_10', '#skF_9', '#skF_9', D_175, E_176) | ~r2_hidden(k4_tarski(D_175, E_176), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_263])).
% 3.48/1.59  tff(c_348, plain, (![A_100, B_101]: (k1_funct_1('#skF_9', '#skF_7'(A_100, B_101, '#skF_9'))='#skF_1'('#skF_10', '#skF_9', '#skF_9', '#skF_7'(A_100, B_101, '#skF_9'), A_100) | ~r2_hidden(A_100, k9_relat_1('#skF_9', B_101)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_24, c_329])).
% 3.48/1.59  tff(c_575, plain, (![A_189, B_190]: (k1_funct_1('#skF_9', '#skF_7'(A_189, B_190, '#skF_9'))='#skF_1'('#skF_10', '#skF_9', '#skF_9', '#skF_7'(A_189, B_190, '#skF_9'), A_189) | ~r2_hidden(A_189, k9_relat_1('#skF_9', B_190)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_348])).
% 3.48/1.59  tff(c_599, plain, (![A_189]: (k1_funct_1('#skF_9', '#skF_7'(A_189, k1_relat_1('#skF_9'), '#skF_9'))='#skF_1'('#skF_10', '#skF_9', '#skF_9', '#skF_7'(A_189, k1_relat_1('#skF_9'), '#skF_9'), A_189) | ~r2_hidden(A_189, k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_575])).
% 3.48/1.59  tff(c_768, plain, (![A_200]: (k1_funct_1('#skF_9', '#skF_7'(A_200, k1_relat_1('#skF_9'), '#skF_9'))='#skF_1'('#skF_10', '#skF_9', '#skF_9', '#skF_7'(A_200, k1_relat_1('#skF_9'), '#skF_9'), A_200) | ~r2_hidden(A_200, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_599])).
% 3.48/1.59  tff(c_80, plain, (![A_132, B_133, C_134]: (r2_hidden(k4_tarski('#skF_7'(A_132, B_133, C_134), A_132), C_134) | ~r2_hidden(A_132, k9_relat_1(C_134, B_133)) | ~v1_relat_1(C_134))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.48/1.59  tff(c_100, plain, (![C_138, A_139, B_140]: (k1_funct_1(C_138, '#skF_7'(A_139, B_140, C_138))=A_139 | ~v1_funct_1(C_138) | ~r2_hidden(A_139, k9_relat_1(C_138, B_140)) | ~v1_relat_1(C_138))), inference(resolution, [status(thm)], [c_80, c_40])).
% 3.48/1.59  tff(c_111, plain, (![A_106, A_139]: (k1_funct_1(A_106, '#skF_7'(A_139, k1_relat_1(A_106), A_106))=A_139 | ~v1_funct_1(A_106) | ~r2_hidden(A_139, k2_relat_1(A_106)) | ~v1_relat_1(A_106) | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_28, c_100])).
% 3.48/1.59  tff(c_801, plain, (![A_200]: ('#skF_1'('#skF_10', '#skF_9', '#skF_9', '#skF_7'(A_200, k1_relat_1('#skF_9'), '#skF_9'), A_200)=A_200 | ~v1_funct_1('#skF_9') | ~r2_hidden(A_200, k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(A_200, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_768, c_111])).
% 3.48/1.59  tff(c_825, plain, (![A_201]: ('#skF_1'('#skF_10', '#skF_9', '#skF_9', '#skF_7'(A_201, k1_relat_1('#skF_9'), '#skF_9'), A_201)=A_201 | ~r2_hidden(A_201, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_48, c_54, c_801])).
% 3.48/1.59  tff(c_151, plain, (![B_153, A_154, D_155, E_156]: (r2_hidden(k4_tarski('#skF_1'(B_153, k5_relat_1(A_154, B_153), A_154, D_155, E_156), E_156), B_153) | ~r2_hidden(k4_tarski(D_155, E_156), k5_relat_1(A_154, B_153)) | ~v1_relat_1(k5_relat_1(A_154, B_153)) | ~v1_relat_1(B_153) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.59  tff(c_167, plain, (![D_155, E_156]: (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9', '#skF_9', D_155, E_156), E_156), '#skF_10') | ~r2_hidden(k4_tarski(D_155, E_156), k5_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_10')) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_151])).
% 3.48/1.59  tff(c_175, plain, (![D_157, E_158]: (r2_hidden(k4_tarski('#skF_1'('#skF_10', '#skF_9', '#skF_9', D_157, E_158), E_158), '#skF_10') | ~r2_hidden(k4_tarski(D_157, E_158), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_56, c_46, c_46, c_167])).
% 3.48/1.59  tff(c_182, plain, (![D_157, E_158]: (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9', '#skF_9', D_157, E_158))=E_158 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(k4_tarski(D_157, E_158), '#skF_9'))), inference(resolution, [status(thm)], [c_175, c_40])).
% 3.48/1.59  tff(c_196, plain, (![D_159, E_160]: (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9', '#skF_9', D_159, E_160))=E_160 | ~r2_hidden(k4_tarski(D_159, E_160), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_182])).
% 3.48/1.59  tff(c_208, plain, (![A_100, B_101]: (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9', '#skF_9', '#skF_7'(A_100, B_101, '#skF_9'), A_100))=A_100 | ~r2_hidden(A_100, k9_relat_1('#skF_9', B_101)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_24, c_196])).
% 3.48/1.59  tff(c_217, plain, (![A_100, B_101]: (k1_funct_1('#skF_10', '#skF_1'('#skF_10', '#skF_9', '#skF_9', '#skF_7'(A_100, B_101, '#skF_9'), A_100))=A_100 | ~r2_hidden(A_100, k9_relat_1('#skF_9', B_101)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_208])).
% 3.48/1.59  tff(c_975, plain, (![A_205]: (k1_funct_1('#skF_10', A_205)=A_205 | ~r2_hidden(A_205, k9_relat_1('#skF_9', k1_relat_1('#skF_9'))) | ~r2_hidden(A_205, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_825, c_217])).
% 3.48/1.59  tff(c_1014, plain, (![A_205]: (k1_funct_1('#skF_10', A_205)=A_205 | ~r2_hidden(A_205, k2_relat_1('#skF_9')) | ~r2_hidden(A_205, k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_975])).
% 3.48/1.59  tff(c_1026, plain, (![A_206]: (k1_funct_1('#skF_10', A_206)=A_206 | ~r2_hidden(A_206, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_1014])).
% 3.48/1.59  tff(c_1057, plain, (k1_funct_1('#skF_10', '#skF_8'(k1_relat_1('#skF_10'), '#skF_10'))='#skF_8'(k1_relat_1('#skF_10'), '#skF_10') | k6_relat_1(k1_relat_1('#skF_10'))='#skF_10' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_32, c_1026])).
% 3.48/1.59  tff(c_1083, plain, (k1_funct_1('#skF_10', '#skF_8'(k1_relat_1('#skF_10'), '#skF_10'))='#skF_8'(k1_relat_1('#skF_10'), '#skF_10') | k6_relat_1(k1_relat_1('#skF_10'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1057])).
% 3.48/1.59  tff(c_1084, plain, (k1_funct_1('#skF_10', '#skF_8'(k1_relat_1('#skF_10'), '#skF_10'))='#skF_8'(k1_relat_1('#skF_10'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_44, c_1083])).
% 3.48/1.59  tff(c_30, plain, (![B_108]: (k1_funct_1(B_108, '#skF_8'(k1_relat_1(B_108), B_108))!='#skF_8'(k1_relat_1(B_108), B_108) | k6_relat_1(k1_relat_1(B_108))=B_108 | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.48/1.59  tff(c_1094, plain, (k6_relat_1(k1_relat_1('#skF_10'))='#skF_10' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1084, c_30])).
% 3.48/1.59  tff(c_1102, plain, (k6_relat_1(k1_relat_1('#skF_10'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1094])).
% 3.48/1.59  tff(c_1104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1102])).
% 3.48/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.59  
% 3.48/1.59  Inference rules
% 3.48/1.59  ----------------------
% 3.48/1.59  #Ref     : 0
% 3.48/1.59  #Sup     : 228
% 3.48/1.59  #Fact    : 0
% 3.48/1.59  #Define  : 0
% 3.48/1.59  #Split   : 0
% 3.48/1.59  #Chain   : 0
% 3.48/1.59  #Close   : 0
% 3.48/1.59  
% 3.48/1.59  Ordering : KBO
% 3.48/1.59  
% 3.48/1.59  Simplification rules
% 3.48/1.59  ----------------------
% 3.48/1.59  #Subsume      : 8
% 3.48/1.59  #Demod        : 97
% 3.48/1.59  #Tautology    : 31
% 3.48/1.59  #SimpNegUnit  : 2
% 3.48/1.59  #BackRed      : 0
% 3.48/1.59  
% 3.48/1.59  #Partial instantiations: 0
% 3.48/1.59  #Strategies tried      : 1
% 3.48/1.59  
% 3.48/1.59  Timing (in seconds)
% 3.48/1.59  ----------------------
% 3.48/1.59  Preprocessing        : 0.35
% 3.48/1.59  Parsing              : 0.17
% 3.48/1.59  CNF conversion       : 0.04
% 3.48/1.59  Main loop            : 0.43
% 3.48/1.59  Inferencing          : 0.16
% 3.48/1.59  Reduction            : 0.12
% 3.48/1.59  Demodulation         : 0.08
% 3.48/1.59  BG Simplification    : 0.03
% 3.48/1.59  Subsumption          : 0.08
% 3.48/1.59  Abstraction          : 0.04
% 3.48/1.59  MUC search           : 0.00
% 3.48/1.59  Cooper               : 0.00
% 3.48/1.59  Total                : 0.81
% 3.48/1.59  Index Insertion      : 0.00
% 3.48/1.59  Index Deletion       : 0.00
% 3.48/1.59  Index Matching       : 0.00
% 3.48/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
