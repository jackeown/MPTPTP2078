%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0644+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:38 EST 2020

% Result     : Theorem 27.02s
% Output     : CNFRefutation 27.14s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 285 expanded)
%              Number of leaves         :   29 ( 114 expanded)
%              Depth                    :   22
%              Number of atoms          :  289 (1067 expanded)
%              Number of equality atoms :   27 ( 144 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
                & v2_funct_1(A) )
             => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
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

tff(f_61,axiom,(
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

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_50,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),k2_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_69,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_70] : r1_tarski(A_70,A_70) ),
    inference(resolution,[status(thm)],[c_69,c_4])).

tff(c_99,plain,(
    ! [A_84,D_85] :
      ( r2_hidden(k1_funct_1(A_84,D_85),k2_relat_1(A_84))
      | ~ r2_hidden(D_85,k1_relat_1(A_84))
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_84,D_85,B_2] :
      ( r2_hidden(k1_funct_1(A_84,D_85),B_2)
      | ~ r1_tarski(k2_relat_1(A_84),B_2)
      | ~ r2_hidden(D_85,k1_relat_1(A_84))
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_52,plain,(
    v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_140,plain,(
    ! [A_95,C_96] :
      ( r2_hidden('#skF_5'(A_95,k2_relat_1(A_95),C_96),k1_relat_1(A_95))
      | ~ r2_hidden(C_96,k2_relat_1(A_95))
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_146,plain,(
    ! [A_95,C_96,B_2] :
      ( r2_hidden('#skF_5'(A_95,k2_relat_1(A_95),C_96),B_2)
      | ~ r1_tarski(k1_relat_1(A_95),B_2)
      | ~ r2_hidden(C_96,k2_relat_1(A_95))
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_10,plain,(
    ! [A_6,C_42] :
      ( k1_funct_1(A_6,'#skF_5'(A_6,k2_relat_1(A_6),C_42)) = C_42
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_418,plain,(
    ! [C_131,B_132,A_133] :
      ( C_131 = B_132
      | k1_funct_1(A_133,C_131) != k1_funct_1(A_133,B_132)
      | ~ r2_hidden(C_131,k1_relat_1(A_133))
      | ~ r2_hidden(B_132,k1_relat_1(A_133))
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_430,plain,(
    ! [C_131,A_6,C_42] :
      ( C_131 = '#skF_5'(A_6,k2_relat_1(A_6),C_42)
      | k1_funct_1(A_6,C_131) != C_42
      | ~ r2_hidden(C_131,k1_relat_1(A_6))
      | ~ r2_hidden('#skF_5'(A_6,k2_relat_1(A_6),C_42),k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6)
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_418])).

tff(c_10178,plain,(
    ! [A_970,C_971] :
      ( '#skF_5'(A_970,k2_relat_1(A_970),k1_funct_1(A_970,C_971)) = C_971
      | ~ r2_hidden(C_971,k1_relat_1(A_970))
      | ~ r2_hidden('#skF_5'(A_970,k2_relat_1(A_970),k1_funct_1(A_970,C_971)),k1_relat_1(A_970))
      | ~ v2_funct_1(A_970)
      | ~ v1_funct_1(A_970)
      | ~ v1_relat_1(A_970)
      | ~ r2_hidden(k1_funct_1(A_970,C_971),k2_relat_1(A_970))
      | ~ v1_funct_1(A_970)
      | ~ v1_relat_1(A_970) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_430])).

tff(c_10263,plain,(
    ! [A_95,C_971] :
      ( '#skF_5'(A_95,k2_relat_1(A_95),k1_funct_1(A_95,C_971)) = C_971
      | ~ r2_hidden(C_971,k1_relat_1(A_95))
      | ~ v2_funct_1(A_95)
      | ~ r1_tarski(k1_relat_1(A_95),k1_relat_1(A_95))
      | ~ r2_hidden(k1_funct_1(A_95,C_971),k2_relat_1(A_95))
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_146,c_10178])).

tff(c_10304,plain,(
    ! [A_972,C_973] :
      ( '#skF_5'(A_972,k2_relat_1(A_972),k1_funct_1(A_972,C_973)) = C_973
      | ~ r2_hidden(C_973,k1_relat_1(A_972))
      | ~ v2_funct_1(A_972)
      | ~ r2_hidden(k1_funct_1(A_972,C_973),k2_relat_1(A_972))
      | ~ v1_funct_1(A_972)
      | ~ v1_relat_1(A_972) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10263])).

tff(c_10375,plain,(
    ! [A_84,D_85] :
      ( '#skF_5'(A_84,k2_relat_1(A_84),k1_funct_1(A_84,D_85)) = D_85
      | ~ v2_funct_1(A_84)
      | ~ r1_tarski(k2_relat_1(A_84),k2_relat_1(A_84))
      | ~ r2_hidden(D_85,k1_relat_1(A_84))
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_105,c_10304])).

tff(c_10429,plain,(
    ! [A_84,D_85] :
      ( '#skF_5'(A_84,k2_relat_1(A_84),k1_funct_1(A_84,D_85)) = D_85
      | ~ v2_funct_1(A_84)
      | ~ r2_hidden(D_85,k1_relat_1(A_84))
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10375])).

tff(c_58,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    ! [A_55,B_56] :
      ( v1_funct_1(k5_relat_1(A_55,B_56))
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    ! [A_53,B_54] :
      ( v1_relat_1(k5_relat_1(A_53,B_54))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,(
    k2_relat_1(k5_relat_1('#skF_9','#skF_8')) = k2_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_104,plain,(
    ! [D_85] :
      ( r2_hidden(k1_funct_1(k5_relat_1('#skF_9','#skF_8'),D_85),k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_85,k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
      | ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_99])).

tff(c_118,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_121,plain,
    ( ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_121])).

tff(c_126,plain,(
    ! [D_85] :
      ( ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8'))
      | r2_hidden(k1_funct_1(k5_relat_1('#skF_9','#skF_8'),D_85),k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_85,k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_177,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_180,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_177])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_62,c_60,c_180])).

tff(c_186,plain,(
    v1_funct_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_127,plain,(
    v1_relat_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_145,plain,(
    ! [C_96] :
      ( r2_hidden('#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_96),k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
      | ~ r2_hidden(C_96,k2_relat_1(k5_relat_1('#skF_9','#skF_8')))
      | ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_140])).

tff(c_148,plain,(
    ! [C_96] :
      ( r2_hidden('#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_96),k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
      | ~ r2_hidden(C_96,k2_relat_1('#skF_8'))
      | ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_54,c_145])).

tff(c_400,plain,(
    ! [C_129] :
      ( r2_hidden('#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_129),k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
      | ~ r2_hidden(C_129,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_148])).

tff(c_46,plain,(
    ! [A_57,C_60,B_58] :
      ( r2_hidden(A_57,k1_relat_1(C_60))
      | ~ r2_hidden(A_57,k1_relat_1(k5_relat_1(C_60,B_58)))
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_403,plain,(
    ! [C_129] :
      ( r2_hidden('#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_129),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_129,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_400,c_46])).

tff(c_408,plain,(
    ! [C_129] :
      ( r2_hidden('#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_129),k1_relat_1('#skF_9'))
      | ~ r2_hidden(C_129,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_403])).

tff(c_399,plain,(
    ! [C_96] :
      ( r2_hidden('#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_96),k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
      | ~ r2_hidden(C_96,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_148])).

tff(c_44,plain,(
    ! [C_60,A_57,B_58] :
      ( r2_hidden(k1_funct_1(C_60,A_57),k1_relat_1(B_58))
      | ~ r2_hidden(A_57,k1_relat_1(k5_relat_1(C_60,B_58)))
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_12,plain,(
    ! [A_6,C_42] :
      ( r2_hidden('#skF_5'(A_6,k2_relat_1(A_6),C_42),k1_relat_1(A_6))
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_769,plain,(
    ! [C_195,B_196,A_197] :
      ( k1_funct_1(k5_relat_1(C_195,B_196),A_197) = k1_funct_1(B_196,k1_funct_1(C_195,A_197))
      | ~ r2_hidden(A_197,k1_relat_1(k5_relat_1(C_195,B_196)))
      | ~ v1_funct_1(C_195)
      | ~ v1_relat_1(C_195)
      | ~ v1_funct_1(B_196)
      | ~ v1_relat_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6986,plain,(
    ! [C_799,B_800,C_801] :
      ( k1_funct_1(k5_relat_1(C_799,B_800),'#skF_5'(k5_relat_1(C_799,B_800),k2_relat_1(k5_relat_1(C_799,B_800)),C_801)) = k1_funct_1(B_800,k1_funct_1(C_799,'#skF_5'(k5_relat_1(C_799,B_800),k2_relat_1(k5_relat_1(C_799,B_800)),C_801)))
      | ~ v1_funct_1(C_799)
      | ~ v1_relat_1(C_799)
      | ~ v1_funct_1(B_800)
      | ~ v1_relat_1(B_800)
      | ~ r2_hidden(C_801,k2_relat_1(k5_relat_1(C_799,B_800)))
      | ~ v1_funct_1(k5_relat_1(C_799,B_800))
      | ~ v1_relat_1(k5_relat_1(C_799,B_800)) ) ),
    inference(resolution,[status(thm)],[c_12,c_769])).

tff(c_40784,plain,(
    ! [B_1649,C_1650,C_1651] :
      ( k1_funct_1(B_1649,k1_funct_1(C_1650,'#skF_5'(k5_relat_1(C_1650,B_1649),k2_relat_1(k5_relat_1(C_1650,B_1649)),C_1651))) = C_1651
      | ~ r2_hidden(C_1651,k2_relat_1(k5_relat_1(C_1650,B_1649)))
      | ~ v1_funct_1(k5_relat_1(C_1650,B_1649))
      | ~ v1_relat_1(k5_relat_1(C_1650,B_1649))
      | ~ v1_funct_1(C_1650)
      | ~ v1_relat_1(C_1650)
      | ~ v1_funct_1(B_1649)
      | ~ v1_relat_1(B_1649)
      | ~ r2_hidden(C_1651,k2_relat_1(k5_relat_1(C_1650,B_1649)))
      | ~ v1_funct_1(k5_relat_1(C_1650,B_1649))
      | ~ v1_relat_1(k5_relat_1(C_1650,B_1649)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6986,c_10])).

tff(c_40935,plain,(
    ! [C_1651] :
      ( k1_funct_1('#skF_8',k1_funct_1('#skF_9','#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1651))) = C_1651
      | ~ r2_hidden(C_1651,k2_relat_1(k5_relat_1('#skF_9','#skF_8')))
      | ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_1651,k2_relat_1(k5_relat_1('#skF_9','#skF_8')))
      | ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_40784])).

tff(c_40993,plain,(
    ! [C_1652] :
      ( k1_funct_1('#skF_8',k1_funct_1('#skF_9','#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1652))) = C_1652
      | ~ r2_hidden(C_1652,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_186,c_54,c_62,c_60,c_58,c_56,c_127,c_186,c_54,c_40935])).

tff(c_41028,plain,(
    ! [C_1652] :
      ( k1_funct_1('#skF_9','#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1652)) = '#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1652)
      | ~ v2_funct_1('#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9','#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1652)),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_1652,k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40993,c_10429])).

tff(c_44421,plain,(
    ! [C_1770] :
      ( k1_funct_1('#skF_9','#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1770)) = '#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1770)
      | ~ r2_hidden(k1_funct_1('#skF_9','#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1770)),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_1770,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_52,c_41028])).

tff(c_44442,plain,(
    ! [C_1770] :
      ( k1_funct_1('#skF_9','#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1770)) = '#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1770)
      | ~ r2_hidden(C_1770,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1770),k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_44421])).

tff(c_44452,plain,(
    ! [C_1771] :
      ( k1_funct_1('#skF_9','#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1771)) = '#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1771)
      | ~ r2_hidden(C_1771,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1771),k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_44442])).

tff(c_44514,plain,(
    ! [C_1772] :
      ( k1_funct_1('#skF_9','#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1772)) = '#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1772)
      | ~ r2_hidden(C_1772,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_399,c_44452])).

tff(c_8,plain,(
    ! [A_6,D_45] :
      ( r2_hidden(k1_funct_1(A_6,D_45),k2_relat_1(A_6))
      | ~ r2_hidden(D_45,k1_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44593,plain,(
    ! [C_1772] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1772),k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1772),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_1772,k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44514,c_8])).

tff(c_44838,plain,(
    ! [C_1779] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1779),k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_5'(k5_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_8'),C_1779),k1_relat_1('#skF_9'))
      | ~ r2_hidden(C_1779,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44593])).

tff(c_45077,plain,(
    ! [C_1781] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_1781),k2_relat_1('#skF_9'))
      | ~ r2_hidden(C_1781,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_408,c_44838])).

tff(c_45083,plain,(
    ! [D_85] :
      ( r2_hidden(D_85,k2_relat_1('#skF_9'))
      | ~ r2_hidden(k1_funct_1('#skF_8',D_85),k2_relat_1('#skF_8'))
      | ~ v2_funct_1('#skF_8')
      | ~ r2_hidden(D_85,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10429,c_45077])).

tff(c_45087,plain,(
    ! [D_1782] :
      ( r2_hidden(D_1782,k2_relat_1('#skF_9'))
      | ~ r2_hidden(k1_funct_1('#skF_8',D_1782),k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_1782,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_52,c_45083])).

tff(c_45171,plain,(
    ! [D_85] :
      ( r2_hidden(D_85,k2_relat_1('#skF_9'))
      | ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_85,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_105,c_45087])).

tff(c_45227,plain,(
    ! [D_1783] :
      ( r2_hidden(D_1783,k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_1783,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_74,c_45171])).

tff(c_45349,plain,(
    ! [A_1788] :
      ( r1_tarski(A_1788,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_1'(A_1788,k2_relat_1('#skF_9')),k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_45227,c_4])).

tff(c_45397,plain,(
    r1_tarski(k1_relat_1('#skF_8'),k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_6,c_45349])).

tff(c_45422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_45397])).

%------------------------------------------------------------------------------
