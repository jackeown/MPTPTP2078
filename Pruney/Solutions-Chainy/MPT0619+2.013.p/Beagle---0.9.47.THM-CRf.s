%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:53 EST 2020

% Result     : Theorem 8.19s
% Output     : CNFRefutation 8.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 155 expanded)
%              Number of leaves         :   34 (  72 expanded)
%              Depth                    :   21
%              Number of atoms          :  147 ( 341 expanded)
%              Number of equality atoms :   70 ( 159 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_68,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_64,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_135,plain,(
    ! [A_84,B_85] :
      ( k9_relat_1(A_84,k1_tarski(B_85)) = k11_relat_1(A_84,B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_148,plain,(
    ! [A_88] :
      ( k9_relat_1(A_88,k1_relat_1('#skF_9')) = k11_relat_1(A_88,'#skF_8')
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_135])).

tff(c_38,plain,(
    ! [A_20] :
      ( k9_relat_1(A_20,k1_relat_1(A_20)) = k2_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_155,plain,
    ( k11_relat_1('#skF_9','#skF_8') = k2_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_38])).

tff(c_165,plain,(
    k11_relat_1('#skF_9','#skF_8') = k2_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_155])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_73,B_74] : k1_enumset1(A_73,A_73,B_74) = k2_tarski(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_112,plain,(
    ! [B_76,A_77] : r2_hidden(B_76,k2_tarski(A_77,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_4])).

tff(c_116,plain,(
    ! [A_78] : r2_hidden(A_78,k1_tarski(A_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_112])).

tff(c_119,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_116])).

tff(c_176,plain,(
    ! [B_93,A_94] :
      ( k11_relat_1(B_93,A_94) != k1_xboole_0
      | ~ r2_hidden(A_94,k1_relat_1(B_93))
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_186,plain,
    ( k11_relat_1('#skF_9','#skF_8') != k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_119,c_176])).

tff(c_191,plain,(
    k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_165,c_186])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_3'(A_14,B_15),A_14)
      | k1_xboole_0 = A_14
      | k1_tarski(B_15) = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    ! [A_23,C_59] :
      ( r2_hidden('#skF_7'(A_23,k2_relat_1(A_23),C_59),k1_relat_1(A_23))
      | ~ r2_hidden(C_59,k2_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    ! [A_23,D_62] :
      ( r2_hidden(k1_funct_1(A_23,D_62),k2_relat_1(A_23))
      | ~ r2_hidden(D_62,k1_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1230,plain,(
    ! [A_164,C_165] :
      ( r2_hidden('#skF_7'(A_164,k2_relat_1(A_164),C_165),k1_relat_1(A_164))
      | ~ r2_hidden(C_165,k2_relat_1(A_164))
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_192,plain,(
    ! [E_95,C_96,B_97,A_98] :
      ( E_95 = C_96
      | E_95 = B_97
      | E_95 = A_98
      | ~ r2_hidden(E_95,k1_enumset1(A_98,B_97,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_216,plain,(
    ! [E_99,B_100,A_101] :
      ( E_99 = B_100
      | E_99 = A_101
      | E_99 = A_101
      | ~ r2_hidden(E_99,k2_tarski(A_101,B_100)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_192])).

tff(c_235,plain,(
    ! [E_102,A_103] :
      ( E_102 = A_103
      | E_102 = A_103
      | E_102 = A_103
      | ~ r2_hidden(E_102,k1_tarski(A_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_216])).

tff(c_245,plain,(
    ! [E_102] :
      ( E_102 = '#skF_8'
      | E_102 = '#skF_8'
      | E_102 = '#skF_8'
      | ~ r2_hidden(E_102,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_235])).

tff(c_1237,plain,(
    ! [C_165] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_165) = '#skF_8'
      | ~ r2_hidden(C_165,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1230,c_245])).

tff(c_1248,plain,(
    ! [C_166] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_166) = '#skF_8'
      | ~ r2_hidden(C_166,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1237])).

tff(c_1252,plain,(
    ! [D_62] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_62)) = '#skF_8'
      | ~ r2_hidden(D_62,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_44,c_1248])).

tff(c_1259,plain,(
    ! [D_62] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_62)) = '#skF_8'
      | ~ r2_hidden(D_62,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1252])).

tff(c_3146,plain,(
    ! [A_4002,C_4003] :
      ( k1_funct_1(A_4002,'#skF_7'(A_4002,k2_relat_1(A_4002),C_4003)) = C_4003
      | ~ r2_hidden(C_4003,k2_relat_1(A_4002))
      | ~ v1_funct_1(A_4002)
      | ~ v1_relat_1(A_4002) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3183,plain,(
    ! [D_62] :
      ( k1_funct_1('#skF_9',D_62) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_62),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_62,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1259,c_3146])).

tff(c_9021,plain,(
    ! [D_13214] :
      ( k1_funct_1('#skF_9',D_13214) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_13214),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_13214,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_3183])).

tff(c_9044,plain,(
    ! [D_62] :
      ( k1_funct_1('#skF_9',D_62) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_62,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_44,c_9021])).

tff(c_9050,plain,(
    ! [D_13400] :
      ( k1_funct_1('#skF_9',D_13400) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_13400,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_9044])).

tff(c_9058,plain,(
    ! [C_59] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_59)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_59,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_48,c_9050])).

tff(c_12786,plain,(
    ! [C_20479] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_20479)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_20479,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_9058])).

tff(c_46,plain,(
    ! [A_23,C_59] :
      ( k1_funct_1(A_23,'#skF_7'(A_23,k2_relat_1(A_23),C_59)) = C_59
      | ~ r2_hidden(C_59,k2_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12840,plain,(
    ! [C_20479] :
      ( k1_funct_1('#skF_9','#skF_8') = C_20479
      | ~ r2_hidden(C_20479,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_20479,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12786,c_46])).

tff(c_12935,plain,(
    ! [C_20665] :
      ( k1_funct_1('#skF_9','#skF_8') = C_20665
      | ~ r2_hidden(C_20665,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_12840])).

tff(c_12969,plain,(
    ! [B_15] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_15) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_15) ) ),
    inference(resolution,[status(thm)],[c_34,c_12935])).

tff(c_12984,plain,(
    ! [B_20851] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_20851) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_tarski(B_20851) ) ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_12969])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( '#skF_3'(A_14,B_15) != B_15
      | k1_xboole_0 = A_14
      | k1_tarski(B_15) = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12995,plain,(
    ! [B_20851] :
      ( k1_funct_1('#skF_9','#skF_8') != B_20851
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_20851)
      | k2_relat_1('#skF_9') = k1_tarski(B_20851) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12984,c_32])).

tff(c_13155,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k2_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_12995])).

tff(c_62,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k2_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_13159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13155,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:31:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.19/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.19/2.73  
% 8.19/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.19/2.73  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 8.19/2.73  
% 8.19/2.73  %Foreground sorts:
% 8.19/2.73  
% 8.19/2.73  
% 8.19/2.73  %Background operators:
% 8.19/2.73  
% 8.19/2.73  
% 8.19/2.73  %Foreground operators:
% 8.19/2.73  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.19/2.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.19/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.19/2.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.19/2.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.19/2.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.19/2.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.19/2.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.19/2.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.19/2.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.19/2.73  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 8.19/2.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.19/2.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.19/2.73  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.19/2.73  tff('#skF_9', type, '#skF_9': $i).
% 8.19/2.73  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 8.19/2.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.19/2.73  tff('#skF_8', type, '#skF_8': $i).
% 8.19/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.19/2.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.19/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.19/2.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 8.19/2.73  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.19/2.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.19/2.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.19/2.73  
% 8.19/2.75  tff(f_100, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 8.19/2.75  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 8.19/2.75  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 8.19/2.75  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.19/2.75  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 8.19/2.75  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 8.19/2.75  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 8.19/2.75  tff(f_60, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 8.19/2.75  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 8.19/2.75  tff(c_68, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.19/2.75  tff(c_64, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.19/2.75  tff(c_135, plain, (![A_84, B_85]: (k9_relat_1(A_84, k1_tarski(B_85))=k11_relat_1(A_84, B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.19/2.75  tff(c_148, plain, (![A_88]: (k9_relat_1(A_88, k1_relat_1('#skF_9'))=k11_relat_1(A_88, '#skF_8') | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_64, c_135])).
% 8.19/2.75  tff(c_38, plain, (![A_20]: (k9_relat_1(A_20, k1_relat_1(A_20))=k2_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.19/2.75  tff(c_155, plain, (k11_relat_1('#skF_9', '#skF_8')=k2_relat_1('#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_148, c_38])).
% 8.19/2.75  tff(c_165, plain, (k11_relat_1('#skF_9', '#skF_8')=k2_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_155])).
% 8.19/2.75  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.19/2.75  tff(c_85, plain, (![A_73, B_74]: (k1_enumset1(A_73, A_73, B_74)=k2_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.19/2.75  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.19/2.75  tff(c_112, plain, (![B_76, A_77]: (r2_hidden(B_76, k2_tarski(A_77, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_4])).
% 8.19/2.75  tff(c_116, plain, (![A_78]: (r2_hidden(A_78, k1_tarski(A_78)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_112])).
% 8.19/2.75  tff(c_119, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_116])).
% 8.19/2.75  tff(c_176, plain, (![B_93, A_94]: (k11_relat_1(B_93, A_94)!=k1_xboole_0 | ~r2_hidden(A_94, k1_relat_1(B_93)) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.19/2.75  tff(c_186, plain, (k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_119, c_176])).
% 8.19/2.75  tff(c_191, plain, (k2_relat_1('#skF_9')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_165, c_186])).
% 8.19/2.75  tff(c_34, plain, (![A_14, B_15]: (r2_hidden('#skF_3'(A_14, B_15), A_14) | k1_xboole_0=A_14 | k1_tarski(B_15)=A_14)), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.19/2.75  tff(c_66, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.19/2.75  tff(c_48, plain, (![A_23, C_59]: (r2_hidden('#skF_7'(A_23, k2_relat_1(A_23), C_59), k1_relat_1(A_23)) | ~r2_hidden(C_59, k2_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.19/2.75  tff(c_44, plain, (![A_23, D_62]: (r2_hidden(k1_funct_1(A_23, D_62), k2_relat_1(A_23)) | ~r2_hidden(D_62, k1_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.19/2.75  tff(c_1230, plain, (![A_164, C_165]: (r2_hidden('#skF_7'(A_164, k2_relat_1(A_164), C_165), k1_relat_1(A_164)) | ~r2_hidden(C_165, k2_relat_1(A_164)) | ~v1_funct_1(A_164) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.19/2.75  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.19/2.75  tff(c_192, plain, (![E_95, C_96, B_97, A_98]: (E_95=C_96 | E_95=B_97 | E_95=A_98 | ~r2_hidden(E_95, k1_enumset1(A_98, B_97, C_96)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.19/2.75  tff(c_216, plain, (![E_99, B_100, A_101]: (E_99=B_100 | E_99=A_101 | E_99=A_101 | ~r2_hidden(E_99, k2_tarski(A_101, B_100)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_192])).
% 8.19/2.75  tff(c_235, plain, (![E_102, A_103]: (E_102=A_103 | E_102=A_103 | E_102=A_103 | ~r2_hidden(E_102, k1_tarski(A_103)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_216])).
% 8.19/2.75  tff(c_245, plain, (![E_102]: (E_102='#skF_8' | E_102='#skF_8' | E_102='#skF_8' | ~r2_hidden(E_102, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_235])).
% 8.19/2.75  tff(c_1237, plain, (![C_165]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_165)='#skF_8' | ~r2_hidden(C_165, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1230, c_245])).
% 8.19/2.75  tff(c_1248, plain, (![C_166]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_166)='#skF_8' | ~r2_hidden(C_166, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1237])).
% 8.19/2.75  tff(c_1252, plain, (![D_62]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_62))='#skF_8' | ~r2_hidden(D_62, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_44, c_1248])).
% 8.19/2.75  tff(c_1259, plain, (![D_62]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_62))='#skF_8' | ~r2_hidden(D_62, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1252])).
% 8.19/2.75  tff(c_3146, plain, (![A_4002, C_4003]: (k1_funct_1(A_4002, '#skF_7'(A_4002, k2_relat_1(A_4002), C_4003))=C_4003 | ~r2_hidden(C_4003, k2_relat_1(A_4002)) | ~v1_funct_1(A_4002) | ~v1_relat_1(A_4002))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.19/2.75  tff(c_3183, plain, (![D_62]: (k1_funct_1('#skF_9', D_62)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_62), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_62, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_1259, c_3146])).
% 8.19/2.75  tff(c_9021, plain, (![D_13214]: (k1_funct_1('#skF_9', D_13214)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_13214), k2_relat_1('#skF_9')) | ~r2_hidden(D_13214, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_3183])).
% 8.19/2.75  tff(c_9044, plain, (![D_62]: (k1_funct_1('#skF_9', D_62)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_62, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_44, c_9021])).
% 8.19/2.75  tff(c_9050, plain, (![D_13400]: (k1_funct_1('#skF_9', D_13400)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_13400, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_9044])).
% 8.19/2.75  tff(c_9058, plain, (![C_59]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_59))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_59, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_9050])).
% 8.19/2.75  tff(c_12786, plain, (![C_20479]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_20479))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_20479, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_9058])).
% 8.19/2.75  tff(c_46, plain, (![A_23, C_59]: (k1_funct_1(A_23, '#skF_7'(A_23, k2_relat_1(A_23), C_59))=C_59 | ~r2_hidden(C_59, k2_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.19/2.75  tff(c_12840, plain, (![C_20479]: (k1_funct_1('#skF_9', '#skF_8')=C_20479 | ~r2_hidden(C_20479, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_20479, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_12786, c_46])).
% 8.19/2.75  tff(c_12935, plain, (![C_20665]: (k1_funct_1('#skF_9', '#skF_8')=C_20665 | ~r2_hidden(C_20665, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_12840])).
% 8.19/2.75  tff(c_12969, plain, (![B_15]: ('#skF_3'(k2_relat_1('#skF_9'), B_15)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_15))), inference(resolution, [status(thm)], [c_34, c_12935])).
% 8.19/2.75  tff(c_12984, plain, (![B_20851]: ('#skF_3'(k2_relat_1('#skF_9'), B_20851)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_tarski(B_20851))), inference(negUnitSimplification, [status(thm)], [c_191, c_12969])).
% 8.19/2.75  tff(c_32, plain, (![A_14, B_15]: ('#skF_3'(A_14, B_15)!=B_15 | k1_xboole_0=A_14 | k1_tarski(B_15)=A_14)), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.19/2.75  tff(c_12995, plain, (![B_20851]: (k1_funct_1('#skF_9', '#skF_8')!=B_20851 | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_20851) | k2_relat_1('#skF_9')=k1_tarski(B_20851))), inference(superposition, [status(thm), theory('equality')], [c_12984, c_32])).
% 8.19/2.75  tff(c_13155, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k2_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_191, c_12995])).
% 8.19/2.75  tff(c_62, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k2_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.19/2.75  tff(c_13159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13155, c_62])).
% 8.19/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.19/2.75  
% 8.19/2.75  Inference rules
% 8.19/2.75  ----------------------
% 8.19/2.75  #Ref     : 8
% 8.19/2.75  #Sup     : 2735
% 8.19/2.75  #Fact    : 5
% 8.19/2.75  #Define  : 0
% 8.19/2.75  #Split   : 8
% 8.19/2.75  #Chain   : 0
% 8.19/2.75  #Close   : 0
% 8.19/2.75  
% 8.19/2.75  Ordering : KBO
% 8.19/2.75  
% 8.19/2.75  Simplification rules
% 8.19/2.75  ----------------------
% 8.19/2.75  #Subsume      : 1272
% 8.19/2.75  #Demod        : 591
% 8.19/2.75  #Tautology    : 713
% 8.19/2.75  #SimpNegUnit  : 214
% 8.19/2.75  #BackRed      : 36
% 8.19/2.75  
% 8.19/2.75  #Partial instantiations: 10735
% 8.19/2.75  #Strategies tried      : 1
% 8.19/2.75  
% 8.19/2.75  Timing (in seconds)
% 8.19/2.75  ----------------------
% 8.19/2.75  Preprocessing        : 0.32
% 8.19/2.75  Parsing              : 0.16
% 8.19/2.75  CNF conversion       : 0.03
% 8.19/2.75  Main loop            : 1.68
% 8.19/2.75  Inferencing          : 0.58
% 8.19/2.75  Reduction            : 0.50
% 8.19/2.75  Demodulation         : 0.35
% 8.19/2.75  BG Simplification    : 0.06
% 8.19/2.75  Subsumption          : 0.46
% 8.19/2.75  Abstraction          : 0.08
% 8.19/2.75  MUC search           : 0.00
% 8.19/2.75  Cooper               : 0.00
% 8.19/2.75  Total                : 2.03
% 8.19/2.75  Index Insertion      : 0.00
% 8.19/2.75  Index Deletion       : 0.00
% 8.19/2.75  Index Matching       : 0.00
% 8.19/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
