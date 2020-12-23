%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:17 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.37s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 415 expanded)
%              Number of leaves         :   27 ( 164 expanded)
%              Depth                    :   14
%              Number of atoms          :  230 (1719 expanded)
%              Number of equality atoms :   30 ( 288 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_8 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k1_relat_1(B))
             => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_102,axiom,(
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

tff(c_52,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_50,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_48,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    ! [A_107,B_108] :
      ( v1_funct_1(k5_relat_1(A_107,B_108))
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108)
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [A_100,B_101] :
      ( v1_relat_1(k5_relat_1(A_100,B_101))
      | ~ v1_relat_1(B_101)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_102,B_105] :
      ( k1_funct_1(A_102,B_105) = k1_xboole_0
      | r2_hidden(B_105,k1_relat_1(A_102))
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_101,plain,(
    ! [C_137,B_138,A_139] :
      ( k1_funct_1(k5_relat_1(C_137,B_138),A_139) = k1_funct_1(B_138,k1_funct_1(C_137,A_139))
      | ~ r2_hidden(A_139,k1_relat_1(k5_relat_1(C_137,B_138)))
      | ~ v1_funct_1(C_137)
      | ~ v1_relat_1(C_137)
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1298,plain,(
    ! [C_266,B_267,B_268] :
      ( k1_funct_1(k5_relat_1(C_266,B_267),B_268) = k1_funct_1(B_267,k1_funct_1(C_266,B_268))
      | ~ v1_funct_1(C_266)
      | ~ v1_relat_1(C_266)
      | ~ v1_funct_1(B_267)
      | ~ v1_relat_1(B_267)
      | k1_funct_1(k5_relat_1(C_266,B_267),B_268) = k1_xboole_0
      | ~ v1_funct_1(k5_relat_1(C_266,B_267))
      | ~ v1_relat_1(k5_relat_1(C_266,B_267)) ) ),
    inference(resolution,[status(thm)],[c_28,c_101])).

tff(c_1302,plain,(
    ! [A_269,B_270,B_271] :
      ( k1_funct_1(k5_relat_1(A_269,B_270),B_271) = k1_funct_1(B_270,k1_funct_1(A_269,B_271))
      | ~ v1_funct_1(A_269)
      | ~ v1_funct_1(B_270)
      | k1_funct_1(k5_relat_1(A_269,B_270),B_271) = k1_xboole_0
      | ~ v1_funct_1(k5_relat_1(A_269,B_270))
      | ~ v1_relat_1(B_270)
      | ~ v1_relat_1(A_269) ) ),
    inference(resolution,[status(thm)],[c_20,c_1298])).

tff(c_1310,plain,(
    ! [A_272,B_273,B_274] :
      ( k1_funct_1(k5_relat_1(A_272,B_273),B_274) = k1_funct_1(B_273,k1_funct_1(A_272,B_274))
      | k1_funct_1(k5_relat_1(A_272,B_273),B_274) = k1_xboole_0
      | ~ v1_funct_1(B_273)
      | ~ v1_relat_1(B_273)
      | ~ v1_funct_1(A_272)
      | ~ v1_relat_1(A_272) ) ),
    inference(resolution,[status(thm)],[c_30,c_1302])).

tff(c_42,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_9'),'#skF_7') != k1_funct_1('#skF_9',k1_funct_1('#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1357,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_9'),'#skF_7') = k1_xboole_0
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1310,c_42])).

tff(c_1396,plain,(
    k1_funct_1(k5_relat_1('#skF_8','#skF_9'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1357])).

tff(c_1398,plain,(
    k1_funct_1('#skF_9',k1_funct_1('#skF_8','#skF_7')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_42])).

tff(c_44,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    ! [A_113,C_115] :
      ( r2_hidden(k4_tarski(A_113,k1_funct_1(C_115,A_113)),C_115)
      | ~ r2_hidden(A_113,k1_relat_1(C_115))
      | ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1409,plain,
    ( r2_hidden(k4_tarski('#skF_7',k1_xboole_0),k5_relat_1('#skF_8','#skF_9'))
    | ~ r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_8','#skF_9')))
    | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_9'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1396,c_36])).

tff(c_1583,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1409])).

tff(c_1587,plain,
    ( ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_20,c_1583])).

tff(c_1591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1587])).

tff(c_1593,plain,(
    v1_relat_1(k5_relat_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1409])).

tff(c_141,plain,(
    ! [D_149,B_150,A_151,E_152] :
      ( r2_hidden(k4_tarski(D_149,'#skF_1'(B_150,k5_relat_1(A_151,B_150),A_151,D_149,E_152)),A_151)
      | ~ r2_hidden(k4_tarski(D_149,E_152),k5_relat_1(A_151,B_150))
      | ~ v1_relat_1(k5_relat_1(A_151,B_150))
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ! [A_113,C_115,B_114] :
      ( r2_hidden(A_113,k1_relat_1(C_115))
      | ~ r2_hidden(k4_tarski(A_113,B_114),C_115)
      | ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_158,plain,(
    ! [D_153,A_154,E_155,B_156] :
      ( r2_hidden(D_153,k1_relat_1(A_154))
      | ~ v1_funct_1(A_154)
      | ~ r2_hidden(k4_tarski(D_153,E_155),k5_relat_1(A_154,B_156))
      | ~ v1_relat_1(k5_relat_1(A_154,B_156))
      | ~ v1_relat_1(B_156)
      | ~ v1_relat_1(A_154) ) ),
    inference(resolution,[status(thm)],[c_141,c_40])).

tff(c_196,plain,(
    ! [A_160,A_161,B_162] :
      ( r2_hidden(A_160,k1_relat_1(A_161))
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(B_162)
      | ~ v1_relat_1(A_161)
      | ~ r2_hidden(A_160,k1_relat_1(k5_relat_1(A_161,B_162)))
      | ~ v1_funct_1(k5_relat_1(A_161,B_162))
      | ~ v1_relat_1(k5_relat_1(A_161,B_162)) ) ),
    inference(resolution,[status(thm)],[c_36,c_158])).

tff(c_222,plain,(
    ! [B_163,A_164,B_165] :
      ( r2_hidden(B_163,k1_relat_1(A_164))
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(B_165)
      | ~ v1_relat_1(A_164)
      | k1_funct_1(k5_relat_1(A_164,B_165),B_163) = k1_xboole_0
      | ~ v1_funct_1(k5_relat_1(A_164,B_165))
      | ~ v1_relat_1(k5_relat_1(A_164,B_165)) ) ),
    inference(resolution,[status(thm)],[c_28,c_196])).

tff(c_226,plain,(
    ! [B_166,A_167,B_168] :
      ( r2_hidden(B_166,k1_relat_1(A_167))
      | ~ v1_funct_1(A_167)
      | k1_funct_1(k5_relat_1(A_167,B_168),B_166) = k1_xboole_0
      | ~ v1_funct_1(k5_relat_1(A_167,B_168))
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(A_167) ) ),
    inference(resolution,[status(thm)],[c_20,c_222])).

tff(c_229,plain,(
    ! [B_166,A_107,B_108] :
      ( r2_hidden(B_166,k1_relat_1(A_107))
      | k1_funct_1(k5_relat_1(A_107,B_108),B_166) = k1_xboole_0
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108)
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_30,c_226])).

tff(c_1592,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_8','#skF_9'))
    | ~ r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_8','#skF_9')))
    | r2_hidden(k4_tarski('#skF_7',k1_xboole_0),k5_relat_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1409])).

tff(c_1594,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_8','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_1592])).

tff(c_1597,plain,(
    ! [B_108] :
      ( k1_funct_1(k5_relat_1(k5_relat_1('#skF_8','#skF_9'),B_108),'#skF_7') = k1_xboole_0
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108)
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_9'))
      | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_229,c_1594])).

tff(c_1603,plain,(
    ! [B_108] :
      ( k1_funct_1(k5_relat_1(k5_relat_1('#skF_8','#skF_9'),B_108),'#skF_7') = k1_xboole_0
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108)
      | ~ v1_funct_1(k5_relat_1('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1593,c_1597])).

tff(c_1607,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1603])).

tff(c_1631,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_30,c_1607])).

tff(c_1635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1631])).

tff(c_1637,plain,(
    v1_funct_1(k5_relat_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1603])).

tff(c_112,plain,(
    ! [B_140,A_141,E_144,D_142,F_143] :
      ( r2_hidden(k4_tarski(D_142,E_144),k5_relat_1(A_141,B_140))
      | ~ r2_hidden(k4_tarski(F_143,E_144),B_140)
      | ~ r2_hidden(k4_tarski(D_142,F_143),A_141)
      | ~ v1_relat_1(k5_relat_1(A_141,B_140))
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_424,plain,(
    ! [D_187,C_188,A_189,A_190] :
      ( r2_hidden(k4_tarski(D_187,k1_funct_1(C_188,A_189)),k5_relat_1(A_190,C_188))
      | ~ r2_hidden(k4_tarski(D_187,A_189),A_190)
      | ~ v1_relat_1(k5_relat_1(A_190,C_188))
      | ~ v1_relat_1(A_190)
      | ~ r2_hidden(A_189,k1_relat_1(C_188))
      | ~ v1_funct_1(C_188)
      | ~ v1_relat_1(C_188) ) ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_577,plain,(
    ! [D_202,A_203,C_204,A_205] :
      ( r2_hidden(D_202,k1_relat_1(k5_relat_1(A_203,C_204)))
      | ~ v1_funct_1(k5_relat_1(A_203,C_204))
      | ~ r2_hidden(k4_tarski(D_202,A_205),A_203)
      | ~ v1_relat_1(k5_relat_1(A_203,C_204))
      | ~ v1_relat_1(A_203)
      | ~ r2_hidden(A_205,k1_relat_1(C_204))
      | ~ v1_funct_1(C_204)
      | ~ v1_relat_1(C_204) ) ),
    inference(resolution,[status(thm)],[c_424,c_40])).

tff(c_1952,plain,(
    ! [A_299,C_300,C_301] :
      ( r2_hidden(A_299,k1_relat_1(k5_relat_1(C_300,C_301)))
      | ~ v1_funct_1(k5_relat_1(C_300,C_301))
      | ~ v1_relat_1(k5_relat_1(C_300,C_301))
      | ~ r2_hidden(k1_funct_1(C_300,A_299),k1_relat_1(C_301))
      | ~ v1_funct_1(C_301)
      | ~ v1_relat_1(C_301)
      | ~ r2_hidden(A_299,k1_relat_1(C_300))
      | ~ v1_funct_1(C_300)
      | ~ v1_relat_1(C_300) ) ),
    inference(resolution,[status(thm)],[c_36,c_577])).

tff(c_2213,plain,(
    ! [A_308,C_309,A_310] :
      ( r2_hidden(A_308,k1_relat_1(k5_relat_1(C_309,A_310)))
      | ~ v1_funct_1(k5_relat_1(C_309,A_310))
      | ~ v1_relat_1(k5_relat_1(C_309,A_310))
      | ~ r2_hidden(A_308,k1_relat_1(C_309))
      | ~ v1_funct_1(C_309)
      | ~ v1_relat_1(C_309)
      | k1_funct_1(A_310,k1_funct_1(C_309,A_308)) = k1_xboole_0
      | ~ v1_funct_1(A_310)
      | ~ v1_relat_1(A_310) ) ),
    inference(resolution,[status(thm)],[c_28,c_1952])).

tff(c_2227,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_8','#skF_9'))
    | ~ v1_relat_1(k5_relat_1('#skF_8','#skF_9'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | k1_funct_1('#skF_9',k1_funct_1('#skF_8','#skF_7')) = k1_xboole_0
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2213,c_1594])).

tff(c_2275,plain,(
    k1_funct_1('#skF_9',k1_funct_1('#skF_8','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_52,c_50,c_44,c_1593,c_1637,c_2227])).

tff(c_2277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1398,c_2275])).

tff(c_2279,plain,(
    r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_8','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_1592])).

tff(c_34,plain,(
    ! [C_112,B_110,A_109] :
      ( k1_funct_1(k5_relat_1(C_112,B_110),A_109) = k1_funct_1(B_110,k1_funct_1(C_112,A_109))
      | ~ r2_hidden(A_109,k1_relat_1(k5_relat_1(C_112,B_110)))
      | ~ v1_funct_1(C_112)
      | ~ v1_relat_1(C_112)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2285,plain,
    ( k1_funct_1(k5_relat_1('#skF_8','#skF_9'),'#skF_7') = k1_funct_1('#skF_9',k1_funct_1('#skF_8','#skF_7'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2279,c_34])).

tff(c_2291,plain,(
    k1_funct_1('#skF_9',k1_funct_1('#skF_8','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_52,c_50,c_1396,c_2285])).

tff(c_2293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1398,c_2291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:46:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/1.98  
% 5.37/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/1.98  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_8 > #skF_3
% 5.37/1.98  
% 5.37/1.98  %Foreground sorts:
% 5.37/1.98  
% 5.37/1.98  
% 5.37/1.98  %Background operators:
% 5.37/1.98  
% 5.37/1.98  
% 5.37/1.98  %Foreground operators:
% 5.37/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.37/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.37/1.98  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.37/1.98  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.37/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.37/1.98  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.37/1.98  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.37/1.98  tff('#skF_7', type, '#skF_7': $i).
% 5.37/1.98  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.37/1.98  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.37/1.98  tff('#skF_9', type, '#skF_9': $i).
% 5.37/1.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.37/1.98  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 5.37/1.98  tff('#skF_8', type, '#skF_8': $i).
% 5.37/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.37/1.98  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.37/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.37/1.98  
% 5.37/2.00  tff(f_116, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 5.37/2.00  tff(f_79, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 5.37/2.00  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.37/2.00  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 5.37/2.00  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 5.37/2.00  tff(f_102, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 5.37/2.00  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 5.37/2.00  tff(c_52, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.37/2.00  tff(c_50, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.37/2.00  tff(c_48, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.37/2.00  tff(c_46, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.37/2.00  tff(c_30, plain, (![A_107, B_108]: (v1_funct_1(k5_relat_1(A_107, B_108)) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.37/2.00  tff(c_20, plain, (![A_100, B_101]: (v1_relat_1(k5_relat_1(A_100, B_101)) | ~v1_relat_1(B_101) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.37/2.00  tff(c_28, plain, (![A_102, B_105]: (k1_funct_1(A_102, B_105)=k1_xboole_0 | r2_hidden(B_105, k1_relat_1(A_102)) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.37/2.00  tff(c_101, plain, (![C_137, B_138, A_139]: (k1_funct_1(k5_relat_1(C_137, B_138), A_139)=k1_funct_1(B_138, k1_funct_1(C_137, A_139)) | ~r2_hidden(A_139, k1_relat_1(k5_relat_1(C_137, B_138))) | ~v1_funct_1(C_137) | ~v1_relat_1(C_137) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.37/2.00  tff(c_1298, plain, (![C_266, B_267, B_268]: (k1_funct_1(k5_relat_1(C_266, B_267), B_268)=k1_funct_1(B_267, k1_funct_1(C_266, B_268)) | ~v1_funct_1(C_266) | ~v1_relat_1(C_266) | ~v1_funct_1(B_267) | ~v1_relat_1(B_267) | k1_funct_1(k5_relat_1(C_266, B_267), B_268)=k1_xboole_0 | ~v1_funct_1(k5_relat_1(C_266, B_267)) | ~v1_relat_1(k5_relat_1(C_266, B_267)))), inference(resolution, [status(thm)], [c_28, c_101])).
% 5.37/2.00  tff(c_1302, plain, (![A_269, B_270, B_271]: (k1_funct_1(k5_relat_1(A_269, B_270), B_271)=k1_funct_1(B_270, k1_funct_1(A_269, B_271)) | ~v1_funct_1(A_269) | ~v1_funct_1(B_270) | k1_funct_1(k5_relat_1(A_269, B_270), B_271)=k1_xboole_0 | ~v1_funct_1(k5_relat_1(A_269, B_270)) | ~v1_relat_1(B_270) | ~v1_relat_1(A_269))), inference(resolution, [status(thm)], [c_20, c_1298])).
% 5.37/2.00  tff(c_1310, plain, (![A_272, B_273, B_274]: (k1_funct_1(k5_relat_1(A_272, B_273), B_274)=k1_funct_1(B_273, k1_funct_1(A_272, B_274)) | k1_funct_1(k5_relat_1(A_272, B_273), B_274)=k1_xboole_0 | ~v1_funct_1(B_273) | ~v1_relat_1(B_273) | ~v1_funct_1(A_272) | ~v1_relat_1(A_272))), inference(resolution, [status(thm)], [c_30, c_1302])).
% 5.37/2.00  tff(c_42, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_9'), '#skF_7')!=k1_funct_1('#skF_9', k1_funct_1('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.37/2.00  tff(c_1357, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_9'), '#skF_7')=k1_xboole_0 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1310, c_42])).
% 5.37/2.00  tff(c_1396, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_9'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_1357])).
% 5.37/2.00  tff(c_1398, plain, (k1_funct_1('#skF_9', k1_funct_1('#skF_8', '#skF_7'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_42])).
% 5.37/2.00  tff(c_44, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.37/2.00  tff(c_36, plain, (![A_113, C_115]: (r2_hidden(k4_tarski(A_113, k1_funct_1(C_115, A_113)), C_115) | ~r2_hidden(A_113, k1_relat_1(C_115)) | ~v1_funct_1(C_115) | ~v1_relat_1(C_115))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.37/2.00  tff(c_1409, plain, (r2_hidden(k4_tarski('#skF_7', k1_xboole_0), k5_relat_1('#skF_8', '#skF_9')) | ~r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_8', '#skF_9'))) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_9')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1396, c_36])).
% 5.37/2.00  tff(c_1583, plain, (~v1_relat_1(k5_relat_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_1409])).
% 5.37/2.00  tff(c_1587, plain, (~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_20, c_1583])).
% 5.37/2.00  tff(c_1591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1587])).
% 5.37/2.00  tff(c_1593, plain, (v1_relat_1(k5_relat_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_1409])).
% 5.37/2.00  tff(c_141, plain, (![D_149, B_150, A_151, E_152]: (r2_hidden(k4_tarski(D_149, '#skF_1'(B_150, k5_relat_1(A_151, B_150), A_151, D_149, E_152)), A_151) | ~r2_hidden(k4_tarski(D_149, E_152), k5_relat_1(A_151, B_150)) | ~v1_relat_1(k5_relat_1(A_151, B_150)) | ~v1_relat_1(B_150) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.37/2.00  tff(c_40, plain, (![A_113, C_115, B_114]: (r2_hidden(A_113, k1_relat_1(C_115)) | ~r2_hidden(k4_tarski(A_113, B_114), C_115) | ~v1_funct_1(C_115) | ~v1_relat_1(C_115))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.37/2.00  tff(c_158, plain, (![D_153, A_154, E_155, B_156]: (r2_hidden(D_153, k1_relat_1(A_154)) | ~v1_funct_1(A_154) | ~r2_hidden(k4_tarski(D_153, E_155), k5_relat_1(A_154, B_156)) | ~v1_relat_1(k5_relat_1(A_154, B_156)) | ~v1_relat_1(B_156) | ~v1_relat_1(A_154))), inference(resolution, [status(thm)], [c_141, c_40])).
% 5.37/2.00  tff(c_196, plain, (![A_160, A_161, B_162]: (r2_hidden(A_160, k1_relat_1(A_161)) | ~v1_funct_1(A_161) | ~v1_relat_1(B_162) | ~v1_relat_1(A_161) | ~r2_hidden(A_160, k1_relat_1(k5_relat_1(A_161, B_162))) | ~v1_funct_1(k5_relat_1(A_161, B_162)) | ~v1_relat_1(k5_relat_1(A_161, B_162)))), inference(resolution, [status(thm)], [c_36, c_158])).
% 5.37/2.00  tff(c_222, plain, (![B_163, A_164, B_165]: (r2_hidden(B_163, k1_relat_1(A_164)) | ~v1_funct_1(A_164) | ~v1_relat_1(B_165) | ~v1_relat_1(A_164) | k1_funct_1(k5_relat_1(A_164, B_165), B_163)=k1_xboole_0 | ~v1_funct_1(k5_relat_1(A_164, B_165)) | ~v1_relat_1(k5_relat_1(A_164, B_165)))), inference(resolution, [status(thm)], [c_28, c_196])).
% 5.37/2.00  tff(c_226, plain, (![B_166, A_167, B_168]: (r2_hidden(B_166, k1_relat_1(A_167)) | ~v1_funct_1(A_167) | k1_funct_1(k5_relat_1(A_167, B_168), B_166)=k1_xboole_0 | ~v1_funct_1(k5_relat_1(A_167, B_168)) | ~v1_relat_1(B_168) | ~v1_relat_1(A_167))), inference(resolution, [status(thm)], [c_20, c_222])).
% 5.37/2.00  tff(c_229, plain, (![B_166, A_107, B_108]: (r2_hidden(B_166, k1_relat_1(A_107)) | k1_funct_1(k5_relat_1(A_107, B_108), B_166)=k1_xboole_0 | ~v1_funct_1(B_108) | ~v1_relat_1(B_108) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_30, c_226])).
% 5.37/2.00  tff(c_1592, plain, (~v1_funct_1(k5_relat_1('#skF_8', '#skF_9')) | ~r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_8', '#skF_9'))) | r2_hidden(k4_tarski('#skF_7', k1_xboole_0), k5_relat_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_1409])).
% 5.37/2.00  tff(c_1594, plain, (~r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_8', '#skF_9')))), inference(splitLeft, [status(thm)], [c_1592])).
% 5.37/2.00  tff(c_1597, plain, (![B_108]: (k1_funct_1(k5_relat_1(k5_relat_1('#skF_8', '#skF_9'), B_108), '#skF_7')=k1_xboole_0 | ~v1_funct_1(B_108) | ~v1_relat_1(B_108) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_9')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_229, c_1594])).
% 5.37/2.00  tff(c_1603, plain, (![B_108]: (k1_funct_1(k5_relat_1(k5_relat_1('#skF_8', '#skF_9'), B_108), '#skF_7')=k1_xboole_0 | ~v1_funct_1(B_108) | ~v1_relat_1(B_108) | ~v1_funct_1(k5_relat_1('#skF_8', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_1593, c_1597])).
% 5.37/2.00  tff(c_1607, plain, (~v1_funct_1(k5_relat_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_1603])).
% 5.37/2.00  tff(c_1631, plain, (~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_30, c_1607])).
% 5.37/2.00  tff(c_1635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_1631])).
% 5.37/2.00  tff(c_1637, plain, (v1_funct_1(k5_relat_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_1603])).
% 5.37/2.00  tff(c_112, plain, (![B_140, A_141, E_144, D_142, F_143]: (r2_hidden(k4_tarski(D_142, E_144), k5_relat_1(A_141, B_140)) | ~r2_hidden(k4_tarski(F_143, E_144), B_140) | ~r2_hidden(k4_tarski(D_142, F_143), A_141) | ~v1_relat_1(k5_relat_1(A_141, B_140)) | ~v1_relat_1(B_140) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.37/2.00  tff(c_424, plain, (![D_187, C_188, A_189, A_190]: (r2_hidden(k4_tarski(D_187, k1_funct_1(C_188, A_189)), k5_relat_1(A_190, C_188)) | ~r2_hidden(k4_tarski(D_187, A_189), A_190) | ~v1_relat_1(k5_relat_1(A_190, C_188)) | ~v1_relat_1(A_190) | ~r2_hidden(A_189, k1_relat_1(C_188)) | ~v1_funct_1(C_188) | ~v1_relat_1(C_188))), inference(resolution, [status(thm)], [c_36, c_112])).
% 5.37/2.00  tff(c_577, plain, (![D_202, A_203, C_204, A_205]: (r2_hidden(D_202, k1_relat_1(k5_relat_1(A_203, C_204))) | ~v1_funct_1(k5_relat_1(A_203, C_204)) | ~r2_hidden(k4_tarski(D_202, A_205), A_203) | ~v1_relat_1(k5_relat_1(A_203, C_204)) | ~v1_relat_1(A_203) | ~r2_hidden(A_205, k1_relat_1(C_204)) | ~v1_funct_1(C_204) | ~v1_relat_1(C_204))), inference(resolution, [status(thm)], [c_424, c_40])).
% 5.37/2.00  tff(c_1952, plain, (![A_299, C_300, C_301]: (r2_hidden(A_299, k1_relat_1(k5_relat_1(C_300, C_301))) | ~v1_funct_1(k5_relat_1(C_300, C_301)) | ~v1_relat_1(k5_relat_1(C_300, C_301)) | ~r2_hidden(k1_funct_1(C_300, A_299), k1_relat_1(C_301)) | ~v1_funct_1(C_301) | ~v1_relat_1(C_301) | ~r2_hidden(A_299, k1_relat_1(C_300)) | ~v1_funct_1(C_300) | ~v1_relat_1(C_300))), inference(resolution, [status(thm)], [c_36, c_577])).
% 5.37/2.00  tff(c_2213, plain, (![A_308, C_309, A_310]: (r2_hidden(A_308, k1_relat_1(k5_relat_1(C_309, A_310))) | ~v1_funct_1(k5_relat_1(C_309, A_310)) | ~v1_relat_1(k5_relat_1(C_309, A_310)) | ~r2_hidden(A_308, k1_relat_1(C_309)) | ~v1_funct_1(C_309) | ~v1_relat_1(C_309) | k1_funct_1(A_310, k1_funct_1(C_309, A_308))=k1_xboole_0 | ~v1_funct_1(A_310) | ~v1_relat_1(A_310))), inference(resolution, [status(thm)], [c_28, c_1952])).
% 5.37/2.00  tff(c_2227, plain, (~v1_funct_1(k5_relat_1('#skF_8', '#skF_9')) | ~v1_relat_1(k5_relat_1('#skF_8', '#skF_9')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | k1_funct_1('#skF_9', k1_funct_1('#skF_8', '#skF_7'))=k1_xboole_0 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_2213, c_1594])).
% 5.37/2.00  tff(c_2275, plain, (k1_funct_1('#skF_9', k1_funct_1('#skF_8', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_52, c_50, c_44, c_1593, c_1637, c_2227])).
% 5.37/2.00  tff(c_2277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1398, c_2275])).
% 5.37/2.00  tff(c_2279, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_1592])).
% 5.37/2.00  tff(c_34, plain, (![C_112, B_110, A_109]: (k1_funct_1(k5_relat_1(C_112, B_110), A_109)=k1_funct_1(B_110, k1_funct_1(C_112, A_109)) | ~r2_hidden(A_109, k1_relat_1(k5_relat_1(C_112, B_110))) | ~v1_funct_1(C_112) | ~v1_relat_1(C_112) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.37/2.00  tff(c_2285, plain, (k1_funct_1(k5_relat_1('#skF_8', '#skF_9'), '#skF_7')=k1_funct_1('#skF_9', k1_funct_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_2279, c_34])).
% 5.37/2.00  tff(c_2291, plain, (k1_funct_1('#skF_9', k1_funct_1('#skF_8', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_52, c_50, c_1396, c_2285])).
% 5.37/2.00  tff(c_2293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1398, c_2291])).
% 5.37/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.00  
% 5.37/2.00  Inference rules
% 5.37/2.00  ----------------------
% 5.37/2.00  #Ref     : 0
% 5.37/2.00  #Sup     : 516
% 5.37/2.00  #Fact    : 1
% 5.37/2.00  #Define  : 0
% 5.37/2.00  #Split   : 5
% 5.37/2.00  #Chain   : 0
% 5.37/2.00  #Close   : 0
% 5.37/2.00  
% 5.37/2.00  Ordering : KBO
% 5.37/2.00  
% 5.37/2.00  Simplification rules
% 5.37/2.00  ----------------------
% 5.37/2.00  #Subsume      : 50
% 5.37/2.00  #Demod        : 112
% 5.37/2.00  #Tautology    : 95
% 5.37/2.00  #SimpNegUnit  : 7
% 5.37/2.00  #BackRed      : 1
% 5.37/2.00  
% 5.37/2.00  #Partial instantiations: 0
% 5.37/2.00  #Strategies tried      : 1
% 5.37/2.00  
% 5.37/2.00  Timing (in seconds)
% 5.37/2.00  ----------------------
% 5.37/2.00  Preprocessing        : 0.32
% 5.37/2.00  Parsing              : 0.17
% 5.37/2.00  CNF conversion       : 0.03
% 5.37/2.00  Main loop            : 0.89
% 5.37/2.00  Inferencing          : 0.30
% 5.37/2.00  Reduction            : 0.21
% 5.37/2.00  Demodulation         : 0.15
% 5.37/2.00  BG Simplification    : 0.05
% 5.37/2.00  Subsumption          : 0.27
% 5.37/2.00  Abstraction          : 0.06
% 5.37/2.00  MUC search           : 0.00
% 5.37/2.00  Cooper               : 0.00
% 5.37/2.00  Total                : 1.25
% 5.37/2.00  Index Insertion      : 0.00
% 5.37/2.00  Index Deletion       : 0.00
% 5.37/2.00  Index Matching       : 0.00
% 5.37/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
