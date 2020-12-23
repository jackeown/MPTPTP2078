%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:16 EST 2020

% Result     : Theorem 30.13s
% Output     : CNFRefutation 30.13s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 264 expanded)
%              Number of leaves         :   24 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  285 (1143 expanded)
%              Number of equality atoms :   14 ( 101 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_8 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
             => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

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

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(c_32,plain,(
    k1_funct_1(k5_relat_1('#skF_9','#skF_8'),'#skF_7') != k1_funct_1('#skF_8',k1_funct_1('#skF_9','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [A_100,B_101] :
      ( v1_relat_1(k5_relat_1(A_100,B_101))
      | ~ v1_relat_1(B_101)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [A_104,C_106] :
      ( r2_hidden(k4_tarski(A_104,k1_funct_1(C_106,A_104)),C_106)
      | ~ r2_hidden(A_104,k1_relat_1(C_106))
      | ~ v1_funct_1(C_106)
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_73,plain,(
    ! [D_129,B_130,A_131,E_132] :
      ( r2_hidden(k4_tarski(D_129,'#skF_1'(B_130,k5_relat_1(A_131,B_130),A_131,D_129,E_132)),A_131)
      | ~ r2_hidden(k4_tarski(D_129,E_132),k5_relat_1(A_131,B_130))
      | ~ v1_relat_1(k5_relat_1(A_131,B_130))
      | ~ v1_relat_1(B_130)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [A_104,C_106,B_105] :
      ( r2_hidden(A_104,k1_relat_1(C_106))
      | ~ r2_hidden(k4_tarski(A_104,B_105),C_106)
      | ~ v1_funct_1(C_106)
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_85,plain,(
    ! [D_133,A_134,E_135,B_136] :
      ( r2_hidden(D_133,k1_relat_1(A_134))
      | ~ v1_funct_1(A_134)
      | ~ r2_hidden(k4_tarski(D_133,E_135),k5_relat_1(A_134,B_136))
      | ~ v1_relat_1(k5_relat_1(A_134,B_136))
      | ~ v1_relat_1(B_136)
      | ~ v1_relat_1(A_134) ) ),
    inference(resolution,[status(thm)],[c_73,c_30])).

tff(c_118,plain,(
    ! [A_140,A_141,B_142] :
      ( r2_hidden(A_140,k1_relat_1(A_141))
      | ~ v1_funct_1(A_141)
      | ~ v1_relat_1(B_142)
      | ~ v1_relat_1(A_141)
      | ~ r2_hidden(A_140,k1_relat_1(k5_relat_1(A_141,B_142)))
      | ~ v1_funct_1(k5_relat_1(A_141,B_142))
      | ~ v1_relat_1(k5_relat_1(A_141,B_142)) ) ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_137,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_118])).

tff(c_144,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_36,c_137])).

tff(c_145,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_148,plain,
    ( ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_20,c_145])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_148])).

tff(c_154,plain,(
    v1_relat_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_40,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    ! [A_102,B_103] :
      ( v1_funct_1(k5_relat_1(A_102,B_103))
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103)
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_153,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8'))
    | r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_155,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_158,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_22,c_155])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_42,c_40,c_158])).

tff(c_164,plain,(
    v1_funct_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_61,plain,(
    ! [B_125,A_126,D_127,E_128] :
      ( r2_hidden(k4_tarski('#skF_1'(B_125,k5_relat_1(A_126,B_125),A_126,D_127,E_128),E_128),B_125)
      | ~ r2_hidden(k4_tarski(D_127,E_128),k5_relat_1(A_126,B_125))
      | ~ v1_relat_1(k5_relat_1(A_126,B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    ! [B_125,A_126,D_127,E_128] :
      ( r2_hidden('#skF_1'(B_125,k5_relat_1(A_126,B_125),A_126,D_127,E_128),k1_relat_1(B_125))
      | ~ v1_funct_1(B_125)
      | ~ r2_hidden(k4_tarski(D_127,E_128),k5_relat_1(A_126,B_125))
      | ~ v1_relat_1(k5_relat_1(A_126,B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_61,c_30])).

tff(c_18,plain,(
    ! [D_92,B_53,A_1,E_93] :
      ( r2_hidden(k4_tarski(D_92,'#skF_1'(B_53,k5_relat_1(A_1,B_53),A_1,D_92,E_93)),A_1)
      | ~ r2_hidden(k4_tarski(D_92,E_93),k5_relat_1(A_1,B_53))
      | ~ v1_relat_1(k5_relat_1(A_1,B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    ! [D_122,A_121,F_123,B_120,E_124] :
      ( r2_hidden(k4_tarski(D_122,E_124),k5_relat_1(A_121,B_120))
      | ~ r2_hidden(k4_tarski(F_123,E_124),B_120)
      | ~ r2_hidden(k4_tarski(D_122,F_123),A_121)
      | ~ v1_relat_1(k5_relat_1(A_121,B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    ! [D_122,C_106,A_104,A_121] :
      ( r2_hidden(k4_tarski(D_122,k1_funct_1(C_106,A_104)),k5_relat_1(A_121,C_106))
      | ~ r2_hidden(k4_tarski(D_122,A_104),A_121)
      | ~ v1_relat_1(k5_relat_1(A_121,C_106))
      | ~ v1_relat_1(A_121)
      | ~ r2_hidden(A_104,k1_relat_1(C_106))
      | ~ v1_funct_1(C_106)
      | ~ v1_relat_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_28,plain,(
    ! [C_106,A_104,B_105] :
      ( k1_funct_1(C_106,A_104) = B_105
      | ~ r2_hidden(k4_tarski(A_104,B_105),C_106)
      | ~ v1_funct_1(C_106)
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_258,plain,(
    ! [B_158,A_159,D_160,E_161] :
      ( '#skF_1'(B_158,k5_relat_1(A_159,B_158),A_159,D_160,E_161) = k1_funct_1(A_159,D_160)
      | ~ v1_funct_1(A_159)
      | ~ r2_hidden(k4_tarski(D_160,E_161),k5_relat_1(A_159,B_158))
      | ~ v1_relat_1(k5_relat_1(A_159,B_158))
      | ~ v1_relat_1(B_158)
      | ~ v1_relat_1(A_159) ) ),
    inference(resolution,[status(thm)],[c_73,c_28])).

tff(c_1054,plain,(
    ! [C_252,A_253,D_254,A_255] :
      ( '#skF_1'(C_252,k5_relat_1(A_253,C_252),A_253,D_254,k1_funct_1(C_252,A_255)) = k1_funct_1(A_253,D_254)
      | ~ v1_funct_1(A_253)
      | ~ r2_hidden(k4_tarski(D_254,A_255),A_253)
      | ~ v1_relat_1(k5_relat_1(A_253,C_252))
      | ~ v1_relat_1(A_253)
      | ~ r2_hidden(A_255,k1_relat_1(C_252))
      | ~ v1_funct_1(C_252)
      | ~ v1_relat_1(C_252) ) ),
    inference(resolution,[status(thm)],[c_60,c_258])).

tff(c_35904,plain,(
    ! [A_1445,D_1446,C_1447,A_1448] :
      ( r2_hidden(k1_funct_1(A_1445,D_1446),k1_relat_1(C_1447))
      | ~ v1_funct_1(C_1447)
      | ~ r2_hidden(k4_tarski(D_1446,k1_funct_1(C_1447,A_1448)),k5_relat_1(A_1445,C_1447))
      | ~ v1_relat_1(k5_relat_1(A_1445,C_1447))
      | ~ v1_relat_1(C_1447)
      | ~ v1_relat_1(A_1445)
      | ~ v1_funct_1(A_1445)
      | ~ r2_hidden(k4_tarski(D_1446,A_1448),A_1445)
      | ~ v1_relat_1(k5_relat_1(A_1445,C_1447))
      | ~ v1_relat_1(A_1445)
      | ~ r2_hidden(A_1448,k1_relat_1(C_1447))
      | ~ v1_funct_1(C_1447)
      | ~ v1_relat_1(C_1447) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1054,c_71])).

tff(c_36060,plain,(
    ! [A_1449,D_1450,C_1451,A_1452] :
      ( r2_hidden(k1_funct_1(A_1449,D_1450),k1_relat_1(C_1451))
      | ~ v1_funct_1(A_1449)
      | ~ r2_hidden(k4_tarski(D_1450,A_1452),A_1449)
      | ~ v1_relat_1(k5_relat_1(A_1449,C_1451))
      | ~ v1_relat_1(A_1449)
      | ~ r2_hidden(A_1452,k1_relat_1(C_1451))
      | ~ v1_funct_1(C_1451)
      | ~ v1_relat_1(C_1451) ) ),
    inference(resolution,[status(thm)],[c_60,c_35904])).

tff(c_37021,plain,(
    ! [D_1471,C_1470,B_1468,A_1469,E_1472] :
      ( r2_hidden(k1_funct_1(A_1469,D_1471),k1_relat_1(C_1470))
      | ~ v1_funct_1(A_1469)
      | ~ v1_relat_1(k5_relat_1(A_1469,C_1470))
      | ~ r2_hidden('#skF_1'(B_1468,k5_relat_1(A_1469,B_1468),A_1469,D_1471,E_1472),k1_relat_1(C_1470))
      | ~ v1_funct_1(C_1470)
      | ~ v1_relat_1(C_1470)
      | ~ r2_hidden(k4_tarski(D_1471,E_1472),k5_relat_1(A_1469,B_1468))
      | ~ v1_relat_1(k5_relat_1(A_1469,B_1468))
      | ~ v1_relat_1(B_1468)
      | ~ v1_relat_1(A_1469) ) ),
    inference(resolution,[status(thm)],[c_18,c_36060])).

tff(c_37369,plain,(
    ! [A_1479,D_1480,B_1481,E_1482] :
      ( r2_hidden(k1_funct_1(A_1479,D_1480),k1_relat_1(B_1481))
      | ~ v1_funct_1(A_1479)
      | ~ v1_funct_1(B_1481)
      | ~ r2_hidden(k4_tarski(D_1480,E_1482),k5_relat_1(A_1479,B_1481))
      | ~ v1_relat_1(k5_relat_1(A_1479,B_1481))
      | ~ v1_relat_1(B_1481)
      | ~ v1_relat_1(A_1479) ) ),
    inference(resolution,[status(thm)],[c_71,c_37021])).

tff(c_37611,plain,(
    ! [A_1483,A_1484,B_1485] :
      ( r2_hidden(k1_funct_1(A_1483,A_1484),k1_relat_1(B_1485))
      | ~ v1_funct_1(A_1483)
      | ~ v1_funct_1(B_1485)
      | ~ v1_relat_1(B_1485)
      | ~ v1_relat_1(A_1483)
      | ~ r2_hidden(A_1484,k1_relat_1(k5_relat_1(A_1483,B_1485)))
      | ~ v1_funct_1(k5_relat_1(A_1483,B_1485))
      | ~ v1_relat_1(k5_relat_1(A_1483,B_1485)) ) ),
    inference(resolution,[status(thm)],[c_26,c_37369])).

tff(c_4565,plain,(
    ! [D_519,A_520,C_521,A_522] :
      ( r2_hidden(k4_tarski(D_519,k1_funct_1(A_520,D_519)),A_520)
      | ~ r2_hidden(k4_tarski(D_519,k1_funct_1(C_521,A_522)),k5_relat_1(A_520,C_521))
      | ~ v1_relat_1(k5_relat_1(A_520,C_521))
      | ~ v1_relat_1(C_521)
      | ~ v1_relat_1(A_520)
      | ~ v1_funct_1(A_520)
      | ~ r2_hidden(k4_tarski(D_519,A_522),A_520)
      | ~ v1_relat_1(k5_relat_1(A_520,C_521))
      | ~ v1_relat_1(A_520)
      | ~ r2_hidden(A_522,k1_relat_1(C_521))
      | ~ v1_funct_1(C_521)
      | ~ v1_relat_1(C_521) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1054,c_18])).

tff(c_4603,plain,(
    ! [D_523,A_524,A_525,C_526] :
      ( r2_hidden(k4_tarski(D_523,k1_funct_1(A_524,D_523)),A_524)
      | ~ v1_funct_1(A_524)
      | ~ r2_hidden(k4_tarski(D_523,A_525),A_524)
      | ~ v1_relat_1(k5_relat_1(A_524,C_526))
      | ~ v1_relat_1(A_524)
      | ~ r2_hidden(A_525,k1_relat_1(C_526))
      | ~ v1_funct_1(C_526)
      | ~ v1_relat_1(C_526) ) ),
    inference(resolution,[status(thm)],[c_60,c_4565])).

tff(c_4712,plain,(
    ! [B_527,D_530,C_528,E_531,A_529] :
      ( r2_hidden(k4_tarski(D_530,k1_funct_1(A_529,D_530)),A_529)
      | ~ v1_funct_1(A_529)
      | ~ v1_relat_1(k5_relat_1(A_529,C_528))
      | ~ r2_hidden('#skF_1'(B_527,k5_relat_1(A_529,B_527),A_529,D_530,E_531),k1_relat_1(C_528))
      | ~ v1_funct_1(C_528)
      | ~ v1_relat_1(C_528)
      | ~ r2_hidden(k4_tarski(D_530,E_531),k5_relat_1(A_529,B_527))
      | ~ v1_relat_1(k5_relat_1(A_529,B_527))
      | ~ v1_relat_1(B_527)
      | ~ v1_relat_1(A_529) ) ),
    inference(resolution,[status(thm)],[c_18,c_4603])).

tff(c_4726,plain,(
    ! [D_532,A_533,B_534,E_535] :
      ( r2_hidden(k4_tarski(D_532,k1_funct_1(A_533,D_532)),A_533)
      | ~ v1_funct_1(A_533)
      | ~ v1_funct_1(B_534)
      | ~ r2_hidden(k4_tarski(D_532,E_535),k5_relat_1(A_533,B_534))
      | ~ v1_relat_1(k5_relat_1(A_533,B_534))
      | ~ v1_relat_1(B_534)
      | ~ v1_relat_1(A_533) ) ),
    inference(resolution,[status(thm)],[c_71,c_4712])).

tff(c_4857,plain,(
    ! [A_536,A_537,B_538] :
      ( r2_hidden(k4_tarski(A_536,k1_funct_1(A_537,A_536)),A_537)
      | ~ v1_funct_1(A_537)
      | ~ v1_funct_1(B_538)
      | ~ v1_relat_1(B_538)
      | ~ v1_relat_1(A_537)
      | ~ r2_hidden(A_536,k1_relat_1(k5_relat_1(A_537,B_538)))
      | ~ v1_funct_1(k5_relat_1(A_537,B_538))
      | ~ v1_relat_1(k5_relat_1(A_537,B_538)) ) ),
    inference(resolution,[status(thm)],[c_26,c_4726])).

tff(c_5024,plain,
    ( r2_hidden(k4_tarski('#skF_7',k1_funct_1('#skF_9','#skF_7')),'#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_4857])).

tff(c_5083,plain,(
    r2_hidden(k4_tarski('#skF_7',k1_funct_1('#skF_9','#skF_7')),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_164,c_38,c_42,c_40,c_36,c_5024])).

tff(c_239,plain,(
    ! [D_154,C_155,A_156,A_157] :
      ( r2_hidden(k4_tarski(D_154,k1_funct_1(C_155,A_156)),k5_relat_1(A_157,C_155))
      | ~ r2_hidden(k4_tarski(D_154,A_156),A_157)
      | ~ v1_relat_1(k5_relat_1(A_157,C_155))
      | ~ v1_relat_1(A_157)
      | ~ r2_hidden(A_156,k1_relat_1(C_155))
      | ~ v1_funct_1(C_155)
      | ~ v1_relat_1(C_155) ) ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_257,plain,(
    ! [A_157,C_155,D_154,A_156] :
      ( k1_funct_1(k5_relat_1(A_157,C_155),D_154) = k1_funct_1(C_155,A_156)
      | ~ v1_funct_1(k5_relat_1(A_157,C_155))
      | ~ r2_hidden(k4_tarski(D_154,A_156),A_157)
      | ~ v1_relat_1(k5_relat_1(A_157,C_155))
      | ~ v1_relat_1(A_157)
      | ~ r2_hidden(A_156,k1_relat_1(C_155))
      | ~ v1_funct_1(C_155)
      | ~ v1_relat_1(C_155) ) ),
    inference(resolution,[status(thm)],[c_239,c_28])).

tff(c_5095,plain,(
    ! [C_155] :
      ( k1_funct_1(k5_relat_1('#skF_9',C_155),'#skF_7') = k1_funct_1(C_155,k1_funct_1('#skF_9','#skF_7'))
      | ~ v1_funct_1(k5_relat_1('#skF_9',C_155))
      | ~ v1_relat_1(k5_relat_1('#skF_9',C_155))
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1(C_155))
      | ~ v1_funct_1(C_155)
      | ~ v1_relat_1(C_155) ) ),
    inference(resolution,[status(thm)],[c_5083,c_257])).

tff(c_5123,plain,(
    ! [C_155] :
      ( k1_funct_1(k5_relat_1('#skF_9',C_155),'#skF_7') = k1_funct_1(C_155,k1_funct_1('#skF_9','#skF_7'))
      | ~ v1_funct_1(k5_relat_1('#skF_9',C_155))
      | ~ v1_relat_1(k5_relat_1('#skF_9',C_155))
      | ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1(C_155))
      | ~ v1_funct_1(C_155)
      | ~ v1_relat_1(C_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5095])).

tff(c_37640,plain,(
    ! [B_1485] :
      ( k1_funct_1(k5_relat_1('#skF_9',B_1485),'#skF_7') = k1_funct_1(B_1485,k1_funct_1('#skF_9','#skF_7'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_funct_1(B_1485)
      | ~ v1_relat_1(B_1485)
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9',B_1485)))
      | ~ v1_funct_1(k5_relat_1('#skF_9',B_1485))
      | ~ v1_relat_1(k5_relat_1('#skF_9',B_1485)) ) ),
    inference(resolution,[status(thm)],[c_37611,c_5123])).

tff(c_37802,plain,(
    ! [B_1486] :
      ( k1_funct_1(k5_relat_1('#skF_9',B_1486),'#skF_7') = k1_funct_1(B_1486,k1_funct_1('#skF_9','#skF_7'))
      | ~ v1_funct_1(B_1486)
      | ~ v1_relat_1(B_1486)
      | ~ r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9',B_1486)))
      | ~ v1_funct_1(k5_relat_1('#skF_9',B_1486))
      | ~ v1_relat_1(k5_relat_1('#skF_9',B_1486)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_37640])).

tff(c_37816,plain,
    ( k1_funct_1(k5_relat_1('#skF_9','#skF_8'),'#skF_7') = k1_funct_1('#skF_8',k1_funct_1('#skF_9','#skF_7'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_funct_1(k5_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_37802])).

tff(c_37826,plain,(
    k1_funct_1(k5_relat_1('#skF_9','#skF_8'),'#skF_7') = k1_funct_1('#skF_8',k1_funct_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_164,c_42,c_40,c_37816])).

tff(c_37828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_37826])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n019.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:11:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.13/19.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.13/19.29  
% 30.13/19.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.13/19.30  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_8 > #skF_3
% 30.13/19.30  
% 30.13/19.30  %Foreground sorts:
% 30.13/19.30  
% 30.13/19.30  
% 30.13/19.30  %Background operators:
% 30.13/19.30  
% 30.13/19.30  
% 30.13/19.30  %Foreground operators:
% 30.13/19.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 30.13/19.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.13/19.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.13/19.30  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 30.13/19.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 30.13/19.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 30.13/19.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 30.13/19.30  tff('#skF_7', type, '#skF_7': $i).
% 30.13/19.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 30.13/19.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 30.13/19.30  tff('#skF_9', type, '#skF_9': $i).
% 30.13/19.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 30.13/19.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 30.13/19.30  tff('#skF_8', type, '#skF_8': $i).
% 30.13/19.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.13/19.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 30.13/19.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 30.13/19.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.13/19.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 30.13/19.30  
% 30.13/19.31  tff(f_85, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 30.13/19.31  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 30.13/19.31  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 30.13/19.31  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 30.13/19.31  tff(f_61, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 30.13/19.31  tff(c_32, plain, (k1_funct_1(k5_relat_1('#skF_9', '#skF_8'), '#skF_7')!=k1_funct_1('#skF_8', k1_funct_1('#skF_9', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.13/19.31  tff(c_38, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.13/19.31  tff(c_42, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.13/19.31  tff(c_20, plain, (![A_100, B_101]: (v1_relat_1(k5_relat_1(A_100, B_101)) | ~v1_relat_1(B_101) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_49])).
% 30.13/19.31  tff(c_36, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.13/19.31  tff(c_34, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.13/19.31  tff(c_26, plain, (![A_104, C_106]: (r2_hidden(k4_tarski(A_104, k1_funct_1(C_106, A_104)), C_106) | ~r2_hidden(A_104, k1_relat_1(C_106)) | ~v1_funct_1(C_106) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_71])).
% 30.13/19.31  tff(c_73, plain, (![D_129, B_130, A_131, E_132]: (r2_hidden(k4_tarski(D_129, '#skF_1'(B_130, k5_relat_1(A_131, B_130), A_131, D_129, E_132)), A_131) | ~r2_hidden(k4_tarski(D_129, E_132), k5_relat_1(A_131, B_130)) | ~v1_relat_1(k5_relat_1(A_131, B_130)) | ~v1_relat_1(B_130) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.13/19.31  tff(c_30, plain, (![A_104, C_106, B_105]: (r2_hidden(A_104, k1_relat_1(C_106)) | ~r2_hidden(k4_tarski(A_104, B_105), C_106) | ~v1_funct_1(C_106) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_71])).
% 30.13/19.31  tff(c_85, plain, (![D_133, A_134, E_135, B_136]: (r2_hidden(D_133, k1_relat_1(A_134)) | ~v1_funct_1(A_134) | ~r2_hidden(k4_tarski(D_133, E_135), k5_relat_1(A_134, B_136)) | ~v1_relat_1(k5_relat_1(A_134, B_136)) | ~v1_relat_1(B_136) | ~v1_relat_1(A_134))), inference(resolution, [status(thm)], [c_73, c_30])).
% 30.13/19.31  tff(c_118, plain, (![A_140, A_141, B_142]: (r2_hidden(A_140, k1_relat_1(A_141)) | ~v1_funct_1(A_141) | ~v1_relat_1(B_142) | ~v1_relat_1(A_141) | ~r2_hidden(A_140, k1_relat_1(k5_relat_1(A_141, B_142))) | ~v1_funct_1(k5_relat_1(A_141, B_142)) | ~v1_relat_1(k5_relat_1(A_141, B_142)))), inference(resolution, [status(thm)], [c_26, c_85])).
% 30.13/19.31  tff(c_137, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_9') | ~v1_funct_1(k5_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_118])).
% 30.13/19.31  tff(c_144, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9')) | ~v1_funct_1(k5_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_36, c_137])).
% 30.13/19.31  tff(c_145, plain, (~v1_relat_1(k5_relat_1('#skF_9', '#skF_8'))), inference(splitLeft, [status(thm)], [c_144])).
% 30.13/19.31  tff(c_148, plain, (~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_20, c_145])).
% 30.13/19.31  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_148])).
% 30.13/19.31  tff(c_154, plain, (v1_relat_1(k5_relat_1('#skF_9', '#skF_8'))), inference(splitRight, [status(thm)], [c_144])).
% 30.13/19.31  tff(c_40, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.13/19.31  tff(c_22, plain, (![A_102, B_103]: (v1_funct_1(k5_relat_1(A_102, B_103)) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_61])).
% 30.13/19.31  tff(c_153, plain, (~v1_funct_1(k5_relat_1('#skF_9', '#skF_8')) | r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_144])).
% 30.13/19.31  tff(c_155, plain, (~v1_funct_1(k5_relat_1('#skF_9', '#skF_8'))), inference(splitLeft, [status(thm)], [c_153])).
% 30.13/19.31  tff(c_158, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_22, c_155])).
% 30.13/19.31  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_42, c_40, c_158])).
% 30.13/19.31  tff(c_164, plain, (v1_funct_1(k5_relat_1('#skF_9', '#skF_8'))), inference(splitRight, [status(thm)], [c_153])).
% 30.13/19.31  tff(c_61, plain, (![B_125, A_126, D_127, E_128]: (r2_hidden(k4_tarski('#skF_1'(B_125, k5_relat_1(A_126, B_125), A_126, D_127, E_128), E_128), B_125) | ~r2_hidden(k4_tarski(D_127, E_128), k5_relat_1(A_126, B_125)) | ~v1_relat_1(k5_relat_1(A_126, B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.13/19.31  tff(c_71, plain, (![B_125, A_126, D_127, E_128]: (r2_hidden('#skF_1'(B_125, k5_relat_1(A_126, B_125), A_126, D_127, E_128), k1_relat_1(B_125)) | ~v1_funct_1(B_125) | ~r2_hidden(k4_tarski(D_127, E_128), k5_relat_1(A_126, B_125)) | ~v1_relat_1(k5_relat_1(A_126, B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_61, c_30])).
% 30.13/19.31  tff(c_18, plain, (![D_92, B_53, A_1, E_93]: (r2_hidden(k4_tarski(D_92, '#skF_1'(B_53, k5_relat_1(A_1, B_53), A_1, D_92, E_93)), A_1) | ~r2_hidden(k4_tarski(D_92, E_93), k5_relat_1(A_1, B_53)) | ~v1_relat_1(k5_relat_1(A_1, B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.13/19.31  tff(c_57, plain, (![D_122, A_121, F_123, B_120, E_124]: (r2_hidden(k4_tarski(D_122, E_124), k5_relat_1(A_121, B_120)) | ~r2_hidden(k4_tarski(F_123, E_124), B_120) | ~r2_hidden(k4_tarski(D_122, F_123), A_121) | ~v1_relat_1(k5_relat_1(A_121, B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.13/19.31  tff(c_60, plain, (![D_122, C_106, A_104, A_121]: (r2_hidden(k4_tarski(D_122, k1_funct_1(C_106, A_104)), k5_relat_1(A_121, C_106)) | ~r2_hidden(k4_tarski(D_122, A_104), A_121) | ~v1_relat_1(k5_relat_1(A_121, C_106)) | ~v1_relat_1(A_121) | ~r2_hidden(A_104, k1_relat_1(C_106)) | ~v1_funct_1(C_106) | ~v1_relat_1(C_106))), inference(resolution, [status(thm)], [c_26, c_57])).
% 30.13/19.31  tff(c_28, plain, (![C_106, A_104, B_105]: (k1_funct_1(C_106, A_104)=B_105 | ~r2_hidden(k4_tarski(A_104, B_105), C_106) | ~v1_funct_1(C_106) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_71])).
% 30.13/19.31  tff(c_258, plain, (![B_158, A_159, D_160, E_161]: ('#skF_1'(B_158, k5_relat_1(A_159, B_158), A_159, D_160, E_161)=k1_funct_1(A_159, D_160) | ~v1_funct_1(A_159) | ~r2_hidden(k4_tarski(D_160, E_161), k5_relat_1(A_159, B_158)) | ~v1_relat_1(k5_relat_1(A_159, B_158)) | ~v1_relat_1(B_158) | ~v1_relat_1(A_159))), inference(resolution, [status(thm)], [c_73, c_28])).
% 30.13/19.31  tff(c_1054, plain, (![C_252, A_253, D_254, A_255]: ('#skF_1'(C_252, k5_relat_1(A_253, C_252), A_253, D_254, k1_funct_1(C_252, A_255))=k1_funct_1(A_253, D_254) | ~v1_funct_1(A_253) | ~r2_hidden(k4_tarski(D_254, A_255), A_253) | ~v1_relat_1(k5_relat_1(A_253, C_252)) | ~v1_relat_1(A_253) | ~r2_hidden(A_255, k1_relat_1(C_252)) | ~v1_funct_1(C_252) | ~v1_relat_1(C_252))), inference(resolution, [status(thm)], [c_60, c_258])).
% 30.13/19.31  tff(c_35904, plain, (![A_1445, D_1446, C_1447, A_1448]: (r2_hidden(k1_funct_1(A_1445, D_1446), k1_relat_1(C_1447)) | ~v1_funct_1(C_1447) | ~r2_hidden(k4_tarski(D_1446, k1_funct_1(C_1447, A_1448)), k5_relat_1(A_1445, C_1447)) | ~v1_relat_1(k5_relat_1(A_1445, C_1447)) | ~v1_relat_1(C_1447) | ~v1_relat_1(A_1445) | ~v1_funct_1(A_1445) | ~r2_hidden(k4_tarski(D_1446, A_1448), A_1445) | ~v1_relat_1(k5_relat_1(A_1445, C_1447)) | ~v1_relat_1(A_1445) | ~r2_hidden(A_1448, k1_relat_1(C_1447)) | ~v1_funct_1(C_1447) | ~v1_relat_1(C_1447))), inference(superposition, [status(thm), theory('equality')], [c_1054, c_71])).
% 30.13/19.31  tff(c_36060, plain, (![A_1449, D_1450, C_1451, A_1452]: (r2_hidden(k1_funct_1(A_1449, D_1450), k1_relat_1(C_1451)) | ~v1_funct_1(A_1449) | ~r2_hidden(k4_tarski(D_1450, A_1452), A_1449) | ~v1_relat_1(k5_relat_1(A_1449, C_1451)) | ~v1_relat_1(A_1449) | ~r2_hidden(A_1452, k1_relat_1(C_1451)) | ~v1_funct_1(C_1451) | ~v1_relat_1(C_1451))), inference(resolution, [status(thm)], [c_60, c_35904])).
% 30.13/19.31  tff(c_37021, plain, (![D_1471, C_1470, B_1468, A_1469, E_1472]: (r2_hidden(k1_funct_1(A_1469, D_1471), k1_relat_1(C_1470)) | ~v1_funct_1(A_1469) | ~v1_relat_1(k5_relat_1(A_1469, C_1470)) | ~r2_hidden('#skF_1'(B_1468, k5_relat_1(A_1469, B_1468), A_1469, D_1471, E_1472), k1_relat_1(C_1470)) | ~v1_funct_1(C_1470) | ~v1_relat_1(C_1470) | ~r2_hidden(k4_tarski(D_1471, E_1472), k5_relat_1(A_1469, B_1468)) | ~v1_relat_1(k5_relat_1(A_1469, B_1468)) | ~v1_relat_1(B_1468) | ~v1_relat_1(A_1469))), inference(resolution, [status(thm)], [c_18, c_36060])).
% 30.13/19.31  tff(c_37369, plain, (![A_1479, D_1480, B_1481, E_1482]: (r2_hidden(k1_funct_1(A_1479, D_1480), k1_relat_1(B_1481)) | ~v1_funct_1(A_1479) | ~v1_funct_1(B_1481) | ~r2_hidden(k4_tarski(D_1480, E_1482), k5_relat_1(A_1479, B_1481)) | ~v1_relat_1(k5_relat_1(A_1479, B_1481)) | ~v1_relat_1(B_1481) | ~v1_relat_1(A_1479))), inference(resolution, [status(thm)], [c_71, c_37021])).
% 30.13/19.31  tff(c_37611, plain, (![A_1483, A_1484, B_1485]: (r2_hidden(k1_funct_1(A_1483, A_1484), k1_relat_1(B_1485)) | ~v1_funct_1(A_1483) | ~v1_funct_1(B_1485) | ~v1_relat_1(B_1485) | ~v1_relat_1(A_1483) | ~r2_hidden(A_1484, k1_relat_1(k5_relat_1(A_1483, B_1485))) | ~v1_funct_1(k5_relat_1(A_1483, B_1485)) | ~v1_relat_1(k5_relat_1(A_1483, B_1485)))), inference(resolution, [status(thm)], [c_26, c_37369])).
% 30.13/19.31  tff(c_4565, plain, (![D_519, A_520, C_521, A_522]: (r2_hidden(k4_tarski(D_519, k1_funct_1(A_520, D_519)), A_520) | ~r2_hidden(k4_tarski(D_519, k1_funct_1(C_521, A_522)), k5_relat_1(A_520, C_521)) | ~v1_relat_1(k5_relat_1(A_520, C_521)) | ~v1_relat_1(C_521) | ~v1_relat_1(A_520) | ~v1_funct_1(A_520) | ~r2_hidden(k4_tarski(D_519, A_522), A_520) | ~v1_relat_1(k5_relat_1(A_520, C_521)) | ~v1_relat_1(A_520) | ~r2_hidden(A_522, k1_relat_1(C_521)) | ~v1_funct_1(C_521) | ~v1_relat_1(C_521))), inference(superposition, [status(thm), theory('equality')], [c_1054, c_18])).
% 30.13/19.31  tff(c_4603, plain, (![D_523, A_524, A_525, C_526]: (r2_hidden(k4_tarski(D_523, k1_funct_1(A_524, D_523)), A_524) | ~v1_funct_1(A_524) | ~r2_hidden(k4_tarski(D_523, A_525), A_524) | ~v1_relat_1(k5_relat_1(A_524, C_526)) | ~v1_relat_1(A_524) | ~r2_hidden(A_525, k1_relat_1(C_526)) | ~v1_funct_1(C_526) | ~v1_relat_1(C_526))), inference(resolution, [status(thm)], [c_60, c_4565])).
% 30.13/19.31  tff(c_4712, plain, (![B_527, D_530, C_528, E_531, A_529]: (r2_hidden(k4_tarski(D_530, k1_funct_1(A_529, D_530)), A_529) | ~v1_funct_1(A_529) | ~v1_relat_1(k5_relat_1(A_529, C_528)) | ~r2_hidden('#skF_1'(B_527, k5_relat_1(A_529, B_527), A_529, D_530, E_531), k1_relat_1(C_528)) | ~v1_funct_1(C_528) | ~v1_relat_1(C_528) | ~r2_hidden(k4_tarski(D_530, E_531), k5_relat_1(A_529, B_527)) | ~v1_relat_1(k5_relat_1(A_529, B_527)) | ~v1_relat_1(B_527) | ~v1_relat_1(A_529))), inference(resolution, [status(thm)], [c_18, c_4603])).
% 30.13/19.31  tff(c_4726, plain, (![D_532, A_533, B_534, E_535]: (r2_hidden(k4_tarski(D_532, k1_funct_1(A_533, D_532)), A_533) | ~v1_funct_1(A_533) | ~v1_funct_1(B_534) | ~r2_hidden(k4_tarski(D_532, E_535), k5_relat_1(A_533, B_534)) | ~v1_relat_1(k5_relat_1(A_533, B_534)) | ~v1_relat_1(B_534) | ~v1_relat_1(A_533))), inference(resolution, [status(thm)], [c_71, c_4712])).
% 30.13/19.31  tff(c_4857, plain, (![A_536, A_537, B_538]: (r2_hidden(k4_tarski(A_536, k1_funct_1(A_537, A_536)), A_537) | ~v1_funct_1(A_537) | ~v1_funct_1(B_538) | ~v1_relat_1(B_538) | ~v1_relat_1(A_537) | ~r2_hidden(A_536, k1_relat_1(k5_relat_1(A_537, B_538))) | ~v1_funct_1(k5_relat_1(A_537, B_538)) | ~v1_relat_1(k5_relat_1(A_537, B_538)))), inference(resolution, [status(thm)], [c_26, c_4726])).
% 30.13/19.31  tff(c_5024, plain, (r2_hidden(k4_tarski('#skF_7', k1_funct_1('#skF_9', '#skF_7')), '#skF_9') | ~v1_funct_1('#skF_9') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_9') | ~v1_funct_1(k5_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_4857])).
% 30.13/19.31  tff(c_5083, plain, (r2_hidden(k4_tarski('#skF_7', k1_funct_1('#skF_9', '#skF_7')), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_164, c_38, c_42, c_40, c_36, c_5024])).
% 30.13/19.31  tff(c_239, plain, (![D_154, C_155, A_156, A_157]: (r2_hidden(k4_tarski(D_154, k1_funct_1(C_155, A_156)), k5_relat_1(A_157, C_155)) | ~r2_hidden(k4_tarski(D_154, A_156), A_157) | ~v1_relat_1(k5_relat_1(A_157, C_155)) | ~v1_relat_1(A_157) | ~r2_hidden(A_156, k1_relat_1(C_155)) | ~v1_funct_1(C_155) | ~v1_relat_1(C_155))), inference(resolution, [status(thm)], [c_26, c_57])).
% 30.13/19.31  tff(c_257, plain, (![A_157, C_155, D_154, A_156]: (k1_funct_1(k5_relat_1(A_157, C_155), D_154)=k1_funct_1(C_155, A_156) | ~v1_funct_1(k5_relat_1(A_157, C_155)) | ~r2_hidden(k4_tarski(D_154, A_156), A_157) | ~v1_relat_1(k5_relat_1(A_157, C_155)) | ~v1_relat_1(A_157) | ~r2_hidden(A_156, k1_relat_1(C_155)) | ~v1_funct_1(C_155) | ~v1_relat_1(C_155))), inference(resolution, [status(thm)], [c_239, c_28])).
% 30.13/19.31  tff(c_5095, plain, (![C_155]: (k1_funct_1(k5_relat_1('#skF_9', C_155), '#skF_7')=k1_funct_1(C_155, k1_funct_1('#skF_9', '#skF_7')) | ~v1_funct_1(k5_relat_1('#skF_9', C_155)) | ~v1_relat_1(k5_relat_1('#skF_9', C_155)) | ~v1_relat_1('#skF_9') | ~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1(C_155)) | ~v1_funct_1(C_155) | ~v1_relat_1(C_155))), inference(resolution, [status(thm)], [c_5083, c_257])).
% 30.13/19.31  tff(c_5123, plain, (![C_155]: (k1_funct_1(k5_relat_1('#skF_9', C_155), '#skF_7')=k1_funct_1(C_155, k1_funct_1('#skF_9', '#skF_7')) | ~v1_funct_1(k5_relat_1('#skF_9', C_155)) | ~v1_relat_1(k5_relat_1('#skF_9', C_155)) | ~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1(C_155)) | ~v1_funct_1(C_155) | ~v1_relat_1(C_155))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5095])).
% 30.13/19.31  tff(c_37640, plain, (![B_1485]: (k1_funct_1(k5_relat_1('#skF_9', B_1485), '#skF_7')=k1_funct_1(B_1485, k1_funct_1('#skF_9', '#skF_7')) | ~v1_funct_1('#skF_9') | ~v1_funct_1(B_1485) | ~v1_relat_1(B_1485) | ~v1_relat_1('#skF_9') | ~r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', B_1485))) | ~v1_funct_1(k5_relat_1('#skF_9', B_1485)) | ~v1_relat_1(k5_relat_1('#skF_9', B_1485)))), inference(resolution, [status(thm)], [c_37611, c_5123])).
% 30.13/19.31  tff(c_37802, plain, (![B_1486]: (k1_funct_1(k5_relat_1('#skF_9', B_1486), '#skF_7')=k1_funct_1(B_1486, k1_funct_1('#skF_9', '#skF_7')) | ~v1_funct_1(B_1486) | ~v1_relat_1(B_1486) | ~r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', B_1486))) | ~v1_funct_1(k5_relat_1('#skF_9', B_1486)) | ~v1_relat_1(k5_relat_1('#skF_9', B_1486)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_37640])).
% 30.13/19.31  tff(c_37816, plain, (k1_funct_1(k5_relat_1('#skF_9', '#skF_8'), '#skF_7')=k1_funct_1('#skF_8', k1_funct_1('#skF_9', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1(k5_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_37802])).
% 30.13/19.31  tff(c_37826, plain, (k1_funct_1(k5_relat_1('#skF_9', '#skF_8'), '#skF_7')=k1_funct_1('#skF_8', k1_funct_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_164, c_42, c_40, c_37816])).
% 30.13/19.31  tff(c_37828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_37826])).
% 30.13/19.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.13/19.31  
% 30.13/19.31  Inference rules
% 30.13/19.31  ----------------------
% 30.13/19.31  #Ref     : 0
% 30.13/19.31  #Sup     : 9585
% 30.13/19.31  #Fact    : 0
% 30.13/19.31  #Define  : 0
% 30.13/19.31  #Split   : 12
% 30.13/19.31  #Chain   : 0
% 30.13/19.31  #Close   : 0
% 30.13/19.31  
% 30.13/19.31  Ordering : KBO
% 30.13/19.31  
% 30.13/19.31  Simplification rules
% 30.13/19.31  ----------------------
% 30.13/19.31  #Subsume      : 1322
% 30.13/19.31  #Demod        : 2873
% 30.13/19.31  #Tautology    : 525
% 30.13/19.31  #SimpNegUnit  : 1
% 30.13/19.31  #BackRed      : 0
% 30.13/19.31  
% 30.13/19.31  #Partial instantiations: 0
% 30.13/19.31  #Strategies tried      : 1
% 30.13/19.31  
% 30.13/19.31  Timing (in seconds)
% 30.13/19.31  ----------------------
% 30.13/19.32  Preprocessing        : 0.29
% 30.13/19.32  Parsing              : 0.15
% 30.13/19.32  CNF conversion       : 0.03
% 30.13/19.32  Main loop            : 18.28
% 30.13/19.32  Inferencing          : 2.35
% 30.13/19.32  Reduction            : 2.19
% 30.13/19.32  Demodulation         : 1.56
% 30.13/19.32  BG Simplification    : 0.37
% 30.13/19.32  Subsumption          : 12.74
% 30.13/19.32  Abstraction          : 0.55
% 30.13/19.32  MUC search           : 0.00
% 30.13/19.32  Cooper               : 0.00
% 30.13/19.32  Total                : 18.60
% 30.13/19.32  Index Insertion      : 0.00
% 30.13/19.32  Index Deletion       : 0.00
% 30.13/19.32  Index Matching       : 0.00
% 30.13/19.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
