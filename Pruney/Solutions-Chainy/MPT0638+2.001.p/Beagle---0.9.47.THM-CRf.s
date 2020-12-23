%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:37 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  116 (1164 expanded)
%              Number of leaves         :   31 ( 461 expanded)
%              Depth                    :   32
%              Number of atoms          :  294 (4749 expanded)
%              Number of equality atoms :  105 (1762 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_13 > #skF_5 > #skF_2 > #skF_8 > #skF_1 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
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

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_76,axiom,(
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
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

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

tff(c_54,plain,(
    k6_relat_1(k1_relat_1('#skF_13')) != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_62,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_60,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    ! [B_146] :
      ( r2_hidden('#skF_11'(k1_relat_1(B_146),B_146),k1_relat_1(B_146))
      | k6_relat_1(k1_relat_1(B_146)) = B_146
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_66,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_64,plain,(
    v1_funct_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_58,plain,(
    k2_relat_1('#skF_12') = k1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_87,plain,(
    ! [A_162,C_163] :
      ( k1_funct_1(A_162,'#skF_10'(A_162,k2_relat_1(A_162),C_163)) = C_163
      | ~ r2_hidden(C_163,k2_relat_1(A_162))
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_106,plain,(
    ! [C_163] :
      ( k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_163)) = C_163
      | ~ r2_hidden(C_163,k2_relat_1('#skF_12'))
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_87])).

tff(c_112,plain,(
    ! [C_163] :
      ( k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_163)) = C_163
      | ~ r2_hidden(C_163,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_106])).

tff(c_26,plain,(
    ! [A_100,B_103] :
      ( k1_funct_1(A_100,B_103) = k1_xboole_0
      | r2_hidden(B_103,k1_relat_1(A_100))
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    ! [A_156,D_157] :
      ( r2_hidden(k1_funct_1(A_156,D_157),k2_relat_1(A_156))
      | ~ r2_hidden(D_157,k1_relat_1(A_156))
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_81,plain,(
    ! [D_157] :
      ( r2_hidden(k1_funct_1('#skF_12',D_157),k1_relat_1('#skF_13'))
      | ~ r2_hidden(D_157,k1_relat_1('#skF_12'))
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_78])).

tff(c_83,plain,(
    ! [D_157] :
      ( r2_hidden(k1_funct_1('#skF_12',D_157),k1_relat_1('#skF_13'))
      | ~ r2_hidden(D_157,k1_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_81])).

tff(c_22,plain,(
    ! [B_103,A_100] :
      ( r2_hidden(k4_tarski(B_103,k1_funct_1(A_100,B_103)),A_100)
      | ~ r2_hidden(B_103,k1_relat_1(A_100))
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    k5_relat_1('#skF_12','#skF_13') = '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_277,plain,(
    ! [D_204,B_205,A_206,E_207] :
      ( r2_hidden(k4_tarski(D_204,'#skF_1'(B_205,k5_relat_1(A_206,B_205),A_206,D_204,E_207)),A_206)
      | ~ r2_hidden(k4_tarski(D_204,E_207),k5_relat_1(A_206,B_205))
      | ~ v1_relat_1(k5_relat_1(A_206,B_205))
      | ~ v1_relat_1(B_205)
      | ~ v1_relat_1(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_288,plain,(
    ! [D_204,E_207] :
      ( r2_hidden(k4_tarski(D_204,'#skF_1'('#skF_13','#skF_12','#skF_12',D_204,E_207)),'#skF_12')
      | ~ r2_hidden(k4_tarski(D_204,E_207),k5_relat_1('#skF_12','#skF_13'))
      | ~ v1_relat_1(k5_relat_1('#skF_12','#skF_13'))
      | ~ v1_relat_1('#skF_13')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_277])).

tff(c_294,plain,(
    ! [D_208,E_209] :
      ( r2_hidden(k4_tarski(D_208,'#skF_1'('#skF_13','#skF_12','#skF_12',D_208,E_209)),'#skF_12')
      | ~ r2_hidden(k4_tarski(D_208,E_209),'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_66,c_56,c_56,c_288])).

tff(c_20,plain,(
    ! [A_100,B_103,C_104] :
      ( k1_funct_1(A_100,B_103) = C_104
      | ~ r2_hidden(k4_tarski(B_103,C_104),A_100)
      | ~ r2_hidden(B_103,k1_relat_1(A_100))
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_299,plain,(
    ! [D_208,E_209] :
      ( k1_funct_1('#skF_12',D_208) = '#skF_1'('#skF_13','#skF_12','#skF_12',D_208,E_209)
      | ~ r2_hidden(D_208,k1_relat_1('#skF_12'))
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12')
      | ~ r2_hidden(k4_tarski(D_208,E_209),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_294,c_20])).

tff(c_306,plain,(
    ! [D_210,E_211] :
      ( k1_funct_1('#skF_12',D_210) = '#skF_1'('#skF_13','#skF_12','#skF_12',D_210,E_211)
      | ~ r2_hidden(D_210,k1_relat_1('#skF_12'))
      | ~ r2_hidden(k4_tarski(D_210,E_211),'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_299])).

tff(c_320,plain,(
    ! [B_103] :
      ( '#skF_1'('#skF_13','#skF_12','#skF_12',B_103,k1_funct_1('#skF_12',B_103)) = k1_funct_1('#skF_12',B_103)
      | ~ r2_hidden(B_103,k1_relat_1('#skF_12'))
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_22,c_306])).

tff(c_329,plain,(
    ! [B_212] :
      ( '#skF_1'('#skF_13','#skF_12','#skF_12',B_212,k1_funct_1('#skF_12',B_212)) = k1_funct_1('#skF_12',B_212)
      | ~ r2_hidden(B_212,k1_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_320])).

tff(c_358,plain,(
    ! [B_103] :
      ( '#skF_1'('#skF_13','#skF_12','#skF_12',B_103,k1_funct_1('#skF_12',B_103)) = k1_funct_1('#skF_12',B_103)
      | k1_funct_1('#skF_12',B_103) = k1_xboole_0
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_26,c_329])).

tff(c_378,plain,(
    ! [B_103] :
      ( '#skF_1'('#skF_13','#skF_12','#skF_12',B_103,k1_funct_1('#skF_12',B_103)) = k1_funct_1('#skF_12',B_103)
      | k1_funct_1('#skF_12',B_103) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_358])).

tff(c_7221,plain,(
    ! [B_363,A_364,D_365,E_366] :
      ( r2_hidden(k4_tarski('#skF_1'(B_363,k5_relat_1(A_364,B_363),A_364,D_365,E_366),E_366),B_363)
      | ~ r2_hidden(k4_tarski(D_365,E_366),k5_relat_1(A_364,B_363))
      | ~ v1_relat_1(k5_relat_1(A_364,B_363))
      | ~ v1_relat_1(B_363)
      | ~ v1_relat_1(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7242,plain,(
    ! [D_365,E_366] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_13','#skF_12','#skF_12',D_365,E_366),E_366),'#skF_13')
      | ~ r2_hidden(k4_tarski(D_365,E_366),k5_relat_1('#skF_12','#skF_13'))
      | ~ v1_relat_1(k5_relat_1('#skF_12','#skF_13'))
      | ~ v1_relat_1('#skF_13')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_7221])).

tff(c_7255,plain,(
    ! [D_367,E_368] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_13','#skF_12','#skF_12',D_367,E_368),E_368),'#skF_13')
      | ~ r2_hidden(k4_tarski(D_367,E_368),'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_66,c_56,c_56,c_7242])).

tff(c_7282,plain,(
    ! [B_369] :
      ( r2_hidden(k4_tarski(k1_funct_1('#skF_12',B_369),k1_funct_1('#skF_12',B_369)),'#skF_13')
      | ~ r2_hidden(k4_tarski(B_369,k1_funct_1('#skF_12',B_369)),'#skF_12')
      | k1_funct_1('#skF_12',B_369) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_7255])).

tff(c_7287,plain,(
    ! [B_369] :
      ( k1_funct_1('#skF_13',k1_funct_1('#skF_12',B_369)) = k1_funct_1('#skF_12',B_369)
      | ~ r2_hidden(k1_funct_1('#skF_12',B_369),k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden(k4_tarski(B_369,k1_funct_1('#skF_12',B_369)),'#skF_12')
      | k1_funct_1('#skF_12',B_369) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7282,c_20])).

tff(c_7499,plain,(
    ! [B_377] :
      ( k1_funct_1('#skF_13',k1_funct_1('#skF_12',B_377)) = k1_funct_1('#skF_12',B_377)
      | ~ r2_hidden(k1_funct_1('#skF_12',B_377),k1_relat_1('#skF_13'))
      | ~ r2_hidden(k4_tarski(B_377,k1_funct_1('#skF_12',B_377)),'#skF_12')
      | k1_funct_1('#skF_12',B_377) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_7287])).

tff(c_7515,plain,(
    ! [B_103] :
      ( k1_funct_1('#skF_13',k1_funct_1('#skF_12',B_103)) = k1_funct_1('#skF_12',B_103)
      | ~ r2_hidden(k1_funct_1('#skF_12',B_103),k1_relat_1('#skF_13'))
      | k1_funct_1('#skF_12',B_103) = k1_xboole_0
      | ~ r2_hidden(B_103,k1_relat_1('#skF_12'))
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_22,c_7499])).

tff(c_7577,plain,(
    ! [B_381] :
      ( k1_funct_1('#skF_13',k1_funct_1('#skF_12',B_381)) = k1_funct_1('#skF_12',B_381)
      | ~ r2_hidden(k1_funct_1('#skF_12',B_381),k1_relat_1('#skF_13'))
      | k1_funct_1('#skF_12',B_381) = k1_xboole_0
      | ~ r2_hidden(B_381,k1_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_7515])).

tff(c_7602,plain,(
    ! [D_382] :
      ( k1_funct_1('#skF_13',k1_funct_1('#skF_12',D_382)) = k1_funct_1('#skF_12',D_382)
      | k1_funct_1('#skF_12',D_382) = k1_xboole_0
      | ~ r2_hidden(D_382,k1_relat_1('#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_83,c_7577])).

tff(c_7654,plain,(
    ! [B_103] :
      ( k1_funct_1('#skF_13',k1_funct_1('#skF_12',B_103)) = k1_funct_1('#skF_12',B_103)
      | k1_funct_1('#skF_12',B_103) = k1_xboole_0
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_26,c_7602])).

tff(c_7679,plain,(
    ! [B_383] :
      ( k1_funct_1('#skF_13',k1_funct_1('#skF_12',B_383)) = k1_funct_1('#skF_12',B_383)
      | k1_funct_1('#skF_12',B_383) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_7654])).

tff(c_7703,plain,(
    ! [C_163] :
      ( k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_163)) = k1_funct_1('#skF_13',C_163)
      | k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_163)) = k1_xboole_0
      | ~ r2_hidden(C_163,k1_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_7679])).

tff(c_7805,plain,(
    ! [C_386] :
      ( ~ r2_hidden(C_386,k1_relat_1('#skF_13'))
      | k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_386)) = k1_xboole_0
      | k1_funct_1('#skF_13',C_386) != k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_7703])).

tff(c_7877,plain,(
    ! [C_387] :
      ( k1_xboole_0 = C_387
      | ~ r2_hidden(C_387,k1_relat_1('#skF_13'))
      | ~ r2_hidden(C_387,k1_relat_1('#skF_13'))
      | k1_funct_1('#skF_13',C_387) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7805,c_112])).

tff(c_7908,plain,
    ( '#skF_11'(k1_relat_1('#skF_13'),'#skF_13') = k1_xboole_0
    | ~ r2_hidden('#skF_11'(k1_relat_1('#skF_13'),'#skF_13'),k1_relat_1('#skF_13'))
    | k1_funct_1('#skF_13','#skF_11'(k1_relat_1('#skF_13'),'#skF_13')) != k1_xboole_0
    | k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_48,c_7877])).

tff(c_7931,plain,
    ( '#skF_11'(k1_relat_1('#skF_13'),'#skF_13') = k1_xboole_0
    | ~ r2_hidden('#skF_11'(k1_relat_1('#skF_13'),'#skF_13'),k1_relat_1('#skF_13'))
    | k1_funct_1('#skF_13','#skF_11'(k1_relat_1('#skF_13'),'#skF_13')) != k1_xboole_0
    | k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_7908])).

tff(c_7932,plain,
    ( '#skF_11'(k1_relat_1('#skF_13'),'#skF_13') = k1_xboole_0
    | ~ r2_hidden('#skF_11'(k1_relat_1('#skF_13'),'#skF_13'),k1_relat_1('#skF_13'))
    | k1_funct_1('#skF_13','#skF_11'(k1_relat_1('#skF_13'),'#skF_13')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_7931])).

tff(c_8029,plain,(
    k1_funct_1('#skF_13','#skF_11'(k1_relat_1('#skF_13'),'#skF_13')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7932])).

tff(c_7724,plain,(
    ! [C_384] :
      ( k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_384)) = k1_funct_1('#skF_13',C_384)
      | k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_384)) = k1_xboole_0
      | ~ r2_hidden(C_384,k1_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_7679])).

tff(c_8031,plain,(
    ! [C_392] :
      ( k1_funct_1('#skF_13',C_392) = C_392
      | ~ r2_hidden(C_392,k1_relat_1('#skF_13'))
      | k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_392)) = k1_xboole_0
      | ~ r2_hidden(C_392,k1_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7724,c_112])).

tff(c_8117,plain,(
    ! [C_393] :
      ( k1_xboole_0 = C_393
      | ~ r2_hidden(C_393,k1_relat_1('#skF_13'))
      | k1_funct_1('#skF_13',C_393) = C_393
      | ~ r2_hidden(C_393,k1_relat_1('#skF_13'))
      | ~ r2_hidden(C_393,k1_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8031,c_112])).

tff(c_8156,plain,(
    ! [B_103] :
      ( k1_xboole_0 = B_103
      | k1_funct_1('#skF_13',B_103) = B_103
      | ~ r2_hidden(B_103,k1_relat_1('#skF_13'))
      | k1_funct_1('#skF_13',B_103) = k1_xboole_0
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_26,c_8117])).

tff(c_8181,plain,(
    ! [B_394] :
      ( k1_xboole_0 = B_394
      | k1_funct_1('#skF_13',B_394) = B_394
      | ~ r2_hidden(B_394,k1_relat_1('#skF_13'))
      | k1_funct_1('#skF_13',B_394) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8156])).

tff(c_8234,plain,(
    ! [B_103] :
      ( k1_xboole_0 = B_103
      | k1_funct_1('#skF_13',B_103) = B_103
      | k1_funct_1('#skF_13',B_103) = k1_xboole_0
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_26,c_8181])).

tff(c_8271,plain,(
    ! [B_395] :
      ( k1_xboole_0 = B_395
      | k1_funct_1('#skF_13',B_395) = B_395
      | k1_funct_1('#skF_13',B_395) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8234])).

tff(c_46,plain,(
    ! [B_146] :
      ( k1_funct_1(B_146,'#skF_11'(k1_relat_1(B_146),B_146)) != '#skF_11'(k1_relat_1(B_146),B_146)
      | k6_relat_1(k1_relat_1(B_146)) = B_146
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8292,plain,
    ( k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13')
    | '#skF_11'(k1_relat_1('#skF_13'),'#skF_13') = k1_xboole_0
    | k1_funct_1('#skF_13','#skF_11'(k1_relat_1('#skF_13'),'#skF_13')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8271,c_46])).

tff(c_8359,plain,
    ( k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13'
    | '#skF_11'(k1_relat_1('#skF_13'),'#skF_13') = k1_xboole_0
    | k1_funct_1('#skF_13','#skF_11'(k1_relat_1('#skF_13'),'#skF_13')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8292])).

tff(c_8360,plain,(
    '#skF_11'(k1_relat_1('#skF_13'),'#skF_13') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_8029,c_54,c_8359])).

tff(c_8381,plain,(
    k1_funct_1('#skF_13',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8360,c_8029])).

tff(c_8388,plain,
    ( r2_hidden(k1_xboole_0,k1_relat_1('#skF_13'))
    | k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_8360,c_48])).

tff(c_8395,plain,
    ( r2_hidden(k1_xboole_0,k1_relat_1('#skF_13'))
    | k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8388])).

tff(c_8396,plain,(
    r2_hidden(k1_xboole_0,k1_relat_1('#skF_13')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_8395])).

tff(c_113,plain,(
    ! [A_164,C_165] :
      ( r2_hidden('#skF_10'(A_164,k2_relat_1(A_164),C_165),k1_relat_1(A_164))
      | ~ r2_hidden(C_165,k2_relat_1(A_164))
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_116,plain,(
    ! [C_165] :
      ( r2_hidden('#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_165),k1_relat_1('#skF_12'))
      | ~ r2_hidden(C_165,k2_relat_1('#skF_12'))
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_113])).

tff(c_118,plain,(
    ! [C_165] :
      ( r2_hidden('#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_165),k1_relat_1('#skF_12'))
      | ~ r2_hidden(C_165,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_116])).

tff(c_119,plain,(
    ! [C_166] :
      ( k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_166)) = C_166
      | ~ r2_hidden(C_166,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_106])).

tff(c_125,plain,(
    ! [C_166] :
      ( r2_hidden(k4_tarski('#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_166),C_166),'#skF_12')
      | ~ r2_hidden('#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_166),k1_relat_1('#skF_12'))
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12')
      | ~ r2_hidden(C_166,k1_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_22])).

tff(c_137,plain,(
    ! [C_166] :
      ( r2_hidden(k4_tarski('#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_166),C_166),'#skF_12')
      | ~ r2_hidden('#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_166),k1_relat_1('#skF_12'))
      | ~ r2_hidden(C_166,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_125])).

tff(c_7339,plain,(
    ! [C_372] :
      ( '#skF_1'('#skF_13','#skF_12','#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_372),k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_372))) = k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_372))
      | ~ r2_hidden(C_372,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_118,c_329])).

tff(c_7404,plain,(
    ! [C_375] :
      ( k1_funct_1('#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_375)) = '#skF_1'('#skF_13','#skF_12','#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_375),C_375)
      | ~ r2_hidden(C_375,k1_relat_1('#skF_13'))
      | ~ r2_hidden(C_375,k1_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_7339])).

tff(c_7475,plain,(
    ! [C_376] :
      ( '#skF_1'('#skF_13','#skF_12','#skF_12','#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_376),C_376) = C_376
      | ~ r2_hidden(C_376,k1_relat_1('#skF_13'))
      | ~ r2_hidden(C_376,k1_relat_1('#skF_13'))
      | ~ r2_hidden(C_376,k1_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7404,c_112])).

tff(c_7254,plain,(
    ! [D_365,E_366] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_13','#skF_12','#skF_12',D_365,E_366),E_366),'#skF_13')
      | ~ r2_hidden(k4_tarski(D_365,E_366),'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_66,c_56,c_56,c_7242])).

tff(c_9237,plain,(
    ! [C_432] :
      ( r2_hidden(k4_tarski(C_432,C_432),'#skF_13')
      | ~ r2_hidden(k4_tarski('#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_432),C_432),'#skF_12')
      | ~ r2_hidden(C_432,k1_relat_1('#skF_13'))
      | ~ r2_hidden(C_432,k1_relat_1('#skF_13'))
      | ~ r2_hidden(C_432,k1_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7475,c_7254])).

tff(c_9242,plain,(
    ! [C_433] :
      ( r2_hidden(k4_tarski(C_433,C_433),'#skF_13')
      | ~ r2_hidden('#skF_10'('#skF_12',k1_relat_1('#skF_13'),C_433),k1_relat_1('#skF_12'))
      | ~ r2_hidden(C_433,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_137,c_9237])).

tff(c_9252,plain,(
    ! [C_434] :
      ( r2_hidden(k4_tarski(C_434,C_434),'#skF_13')
      | ~ r2_hidden(C_434,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_118,c_9242])).

tff(c_9263,plain,(
    ! [C_434] :
      ( k1_funct_1('#skF_13',C_434) = C_434
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden(C_434,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_9252,c_20])).

tff(c_9276,plain,(
    ! [C_435] :
      ( k1_funct_1('#skF_13',C_435) = C_435
      | ~ r2_hidden(C_435,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_9263])).

tff(c_9282,plain,(
    k1_funct_1('#skF_13',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8396,c_9276])).

tff(c_9348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8381,c_9282])).

tff(c_9350,plain,(
    k1_funct_1('#skF_13','#skF_11'(k1_relat_1('#skF_13'),'#skF_13')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7932])).

tff(c_9358,plain,
    ( '#skF_11'(k1_relat_1('#skF_13'),'#skF_13') != k1_xboole_0
    | k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_9350,c_46])).

tff(c_9372,plain,
    ( '#skF_11'(k1_relat_1('#skF_13'),'#skF_13') != k1_xboole_0
    | k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_9358])).

tff(c_9373,plain,(
    '#skF_11'(k1_relat_1('#skF_13'),'#skF_13') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9372])).

tff(c_9349,plain,
    ( ~ r2_hidden('#skF_11'(k1_relat_1('#skF_13'),'#skF_13'),k1_relat_1('#skF_13'))
    | '#skF_11'(k1_relat_1('#skF_13'),'#skF_13') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7932])).

tff(c_9457,plain,(
    ~ r2_hidden('#skF_11'(k1_relat_1('#skF_13'),'#skF_13'),k1_relat_1('#skF_13')) ),
    inference(negUnitSimplification,[status(thm)],[c_9373,c_9349])).

tff(c_9460,plain,
    ( k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_48,c_9457])).

tff(c_9466,plain,(
    k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_9460])).

tff(c_9468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:39:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.87/2.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.87/2.66  
% 7.87/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.87/2.66  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_13 > #skF_5 > #skF_2 > #skF_8 > #skF_1 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10
% 7.87/2.66  
% 7.87/2.66  %Foreground sorts:
% 7.87/2.66  
% 7.87/2.66  
% 7.87/2.66  %Background operators:
% 7.87/2.66  
% 7.87/2.66  
% 7.87/2.66  %Foreground operators:
% 7.87/2.66  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 7.87/2.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.87/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.87/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.87/2.66  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.87/2.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.87/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.87/2.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.87/2.66  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.87/2.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.87/2.66  tff('#skF_13', type, '#skF_13': $i).
% 7.87/2.66  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.87/2.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.87/2.66  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.87/2.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.87/2.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 7.87/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.87/2.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.87/2.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.87/2.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.87/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.87/2.66  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.87/2.66  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 7.87/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.87/2.66  tff('#skF_12', type, '#skF_12': $i).
% 7.87/2.66  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 7.87/2.66  
% 7.87/2.68  tff(f_105, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 7.87/2.68  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 7.87/2.68  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 7.87/2.68  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 7.87/2.68  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 7.87/2.68  tff(c_54, plain, (k6_relat_1(k1_relat_1('#skF_13'))!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.87/2.68  tff(c_62, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.87/2.68  tff(c_60, plain, (v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.87/2.68  tff(c_48, plain, (![B_146]: (r2_hidden('#skF_11'(k1_relat_1(B_146), B_146), k1_relat_1(B_146)) | k6_relat_1(k1_relat_1(B_146))=B_146 | ~v1_funct_1(B_146) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.87/2.68  tff(c_66, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.87/2.68  tff(c_64, plain, (v1_funct_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.87/2.68  tff(c_58, plain, (k2_relat_1('#skF_12')=k1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.87/2.68  tff(c_87, plain, (![A_162, C_163]: (k1_funct_1(A_162, '#skF_10'(A_162, k2_relat_1(A_162), C_163))=C_163 | ~r2_hidden(C_163, k2_relat_1(A_162)) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.87/2.68  tff(c_106, plain, (![C_163]: (k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_163))=C_163 | ~r2_hidden(C_163, k2_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_87])).
% 7.87/2.68  tff(c_112, plain, (![C_163]: (k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_163))=C_163 | ~r2_hidden(C_163, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_106])).
% 7.87/2.68  tff(c_26, plain, (![A_100, B_103]: (k1_funct_1(A_100, B_103)=k1_xboole_0 | r2_hidden(B_103, k1_relat_1(A_100)) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.87/2.68  tff(c_78, plain, (![A_156, D_157]: (r2_hidden(k1_funct_1(A_156, D_157), k2_relat_1(A_156)) | ~r2_hidden(D_157, k1_relat_1(A_156)) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.87/2.68  tff(c_81, plain, (![D_157]: (r2_hidden(k1_funct_1('#skF_12', D_157), k1_relat_1('#skF_13')) | ~r2_hidden(D_157, k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_78])).
% 7.87/2.68  tff(c_83, plain, (![D_157]: (r2_hidden(k1_funct_1('#skF_12', D_157), k1_relat_1('#skF_13')) | ~r2_hidden(D_157, k1_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_81])).
% 7.87/2.68  tff(c_22, plain, (![B_103, A_100]: (r2_hidden(k4_tarski(B_103, k1_funct_1(A_100, B_103)), A_100) | ~r2_hidden(B_103, k1_relat_1(A_100)) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.87/2.68  tff(c_56, plain, (k5_relat_1('#skF_12', '#skF_13')='#skF_12'), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.87/2.68  tff(c_277, plain, (![D_204, B_205, A_206, E_207]: (r2_hidden(k4_tarski(D_204, '#skF_1'(B_205, k5_relat_1(A_206, B_205), A_206, D_204, E_207)), A_206) | ~r2_hidden(k4_tarski(D_204, E_207), k5_relat_1(A_206, B_205)) | ~v1_relat_1(k5_relat_1(A_206, B_205)) | ~v1_relat_1(B_205) | ~v1_relat_1(A_206))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.87/2.68  tff(c_288, plain, (![D_204, E_207]: (r2_hidden(k4_tarski(D_204, '#skF_1'('#skF_13', '#skF_12', '#skF_12', D_204, E_207)), '#skF_12') | ~r2_hidden(k4_tarski(D_204, E_207), k5_relat_1('#skF_12', '#skF_13')) | ~v1_relat_1(k5_relat_1('#skF_12', '#skF_13')) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_277])).
% 7.87/2.68  tff(c_294, plain, (![D_208, E_209]: (r2_hidden(k4_tarski(D_208, '#skF_1'('#skF_13', '#skF_12', '#skF_12', D_208, E_209)), '#skF_12') | ~r2_hidden(k4_tarski(D_208, E_209), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_66, c_56, c_56, c_288])).
% 7.87/2.68  tff(c_20, plain, (![A_100, B_103, C_104]: (k1_funct_1(A_100, B_103)=C_104 | ~r2_hidden(k4_tarski(B_103, C_104), A_100) | ~r2_hidden(B_103, k1_relat_1(A_100)) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.87/2.68  tff(c_299, plain, (![D_208, E_209]: (k1_funct_1('#skF_12', D_208)='#skF_1'('#skF_13', '#skF_12', '#skF_12', D_208, E_209) | ~r2_hidden(D_208, k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12') | ~r2_hidden(k4_tarski(D_208, E_209), '#skF_12'))), inference(resolution, [status(thm)], [c_294, c_20])).
% 7.87/2.68  tff(c_306, plain, (![D_210, E_211]: (k1_funct_1('#skF_12', D_210)='#skF_1'('#skF_13', '#skF_12', '#skF_12', D_210, E_211) | ~r2_hidden(D_210, k1_relat_1('#skF_12')) | ~r2_hidden(k4_tarski(D_210, E_211), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_299])).
% 7.87/2.68  tff(c_320, plain, (![B_103]: ('#skF_1'('#skF_13', '#skF_12', '#skF_12', B_103, k1_funct_1('#skF_12', B_103))=k1_funct_1('#skF_12', B_103) | ~r2_hidden(B_103, k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_22, c_306])).
% 7.87/2.68  tff(c_329, plain, (![B_212]: ('#skF_1'('#skF_13', '#skF_12', '#skF_12', B_212, k1_funct_1('#skF_12', B_212))=k1_funct_1('#skF_12', B_212) | ~r2_hidden(B_212, k1_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_320])).
% 7.87/2.68  tff(c_358, plain, (![B_103]: ('#skF_1'('#skF_13', '#skF_12', '#skF_12', B_103, k1_funct_1('#skF_12', B_103))=k1_funct_1('#skF_12', B_103) | k1_funct_1('#skF_12', B_103)=k1_xboole_0 | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_26, c_329])).
% 7.87/2.68  tff(c_378, plain, (![B_103]: ('#skF_1'('#skF_13', '#skF_12', '#skF_12', B_103, k1_funct_1('#skF_12', B_103))=k1_funct_1('#skF_12', B_103) | k1_funct_1('#skF_12', B_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_358])).
% 7.87/2.68  tff(c_7221, plain, (![B_363, A_364, D_365, E_366]: (r2_hidden(k4_tarski('#skF_1'(B_363, k5_relat_1(A_364, B_363), A_364, D_365, E_366), E_366), B_363) | ~r2_hidden(k4_tarski(D_365, E_366), k5_relat_1(A_364, B_363)) | ~v1_relat_1(k5_relat_1(A_364, B_363)) | ~v1_relat_1(B_363) | ~v1_relat_1(A_364))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.87/2.68  tff(c_7242, plain, (![D_365, E_366]: (r2_hidden(k4_tarski('#skF_1'('#skF_13', '#skF_12', '#skF_12', D_365, E_366), E_366), '#skF_13') | ~r2_hidden(k4_tarski(D_365, E_366), k5_relat_1('#skF_12', '#skF_13')) | ~v1_relat_1(k5_relat_1('#skF_12', '#skF_13')) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_7221])).
% 7.87/2.68  tff(c_7255, plain, (![D_367, E_368]: (r2_hidden(k4_tarski('#skF_1'('#skF_13', '#skF_12', '#skF_12', D_367, E_368), E_368), '#skF_13') | ~r2_hidden(k4_tarski(D_367, E_368), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_66, c_56, c_56, c_7242])).
% 7.87/2.68  tff(c_7282, plain, (![B_369]: (r2_hidden(k4_tarski(k1_funct_1('#skF_12', B_369), k1_funct_1('#skF_12', B_369)), '#skF_13') | ~r2_hidden(k4_tarski(B_369, k1_funct_1('#skF_12', B_369)), '#skF_12') | k1_funct_1('#skF_12', B_369)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_378, c_7255])).
% 7.87/2.68  tff(c_7287, plain, (![B_369]: (k1_funct_1('#skF_13', k1_funct_1('#skF_12', B_369))=k1_funct_1('#skF_12', B_369) | ~r2_hidden(k1_funct_1('#skF_12', B_369), k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden(k4_tarski(B_369, k1_funct_1('#skF_12', B_369)), '#skF_12') | k1_funct_1('#skF_12', B_369)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7282, c_20])).
% 7.87/2.68  tff(c_7499, plain, (![B_377]: (k1_funct_1('#skF_13', k1_funct_1('#skF_12', B_377))=k1_funct_1('#skF_12', B_377) | ~r2_hidden(k1_funct_1('#skF_12', B_377), k1_relat_1('#skF_13')) | ~r2_hidden(k4_tarski(B_377, k1_funct_1('#skF_12', B_377)), '#skF_12') | k1_funct_1('#skF_12', B_377)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_7287])).
% 7.87/2.68  tff(c_7515, plain, (![B_103]: (k1_funct_1('#skF_13', k1_funct_1('#skF_12', B_103))=k1_funct_1('#skF_12', B_103) | ~r2_hidden(k1_funct_1('#skF_12', B_103), k1_relat_1('#skF_13')) | k1_funct_1('#skF_12', B_103)=k1_xboole_0 | ~r2_hidden(B_103, k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_22, c_7499])).
% 7.87/2.68  tff(c_7577, plain, (![B_381]: (k1_funct_1('#skF_13', k1_funct_1('#skF_12', B_381))=k1_funct_1('#skF_12', B_381) | ~r2_hidden(k1_funct_1('#skF_12', B_381), k1_relat_1('#skF_13')) | k1_funct_1('#skF_12', B_381)=k1_xboole_0 | ~r2_hidden(B_381, k1_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_7515])).
% 7.87/2.68  tff(c_7602, plain, (![D_382]: (k1_funct_1('#skF_13', k1_funct_1('#skF_12', D_382))=k1_funct_1('#skF_12', D_382) | k1_funct_1('#skF_12', D_382)=k1_xboole_0 | ~r2_hidden(D_382, k1_relat_1('#skF_12')))), inference(resolution, [status(thm)], [c_83, c_7577])).
% 7.87/2.68  tff(c_7654, plain, (![B_103]: (k1_funct_1('#skF_13', k1_funct_1('#skF_12', B_103))=k1_funct_1('#skF_12', B_103) | k1_funct_1('#skF_12', B_103)=k1_xboole_0 | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_26, c_7602])).
% 7.87/2.68  tff(c_7679, plain, (![B_383]: (k1_funct_1('#skF_13', k1_funct_1('#skF_12', B_383))=k1_funct_1('#skF_12', B_383) | k1_funct_1('#skF_12', B_383)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_7654])).
% 7.87/2.68  tff(c_7703, plain, (![C_163]: (k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_163))=k1_funct_1('#skF_13', C_163) | k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_163))=k1_xboole_0 | ~r2_hidden(C_163, k1_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_112, c_7679])).
% 7.87/2.68  tff(c_7805, plain, (![C_386]: (~r2_hidden(C_386, k1_relat_1('#skF_13')) | k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_386))=k1_xboole_0 | k1_funct_1('#skF_13', C_386)!=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_7703])).
% 7.87/2.68  tff(c_7877, plain, (![C_387]: (k1_xboole_0=C_387 | ~r2_hidden(C_387, k1_relat_1('#skF_13')) | ~r2_hidden(C_387, k1_relat_1('#skF_13')) | k1_funct_1('#skF_13', C_387)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7805, c_112])).
% 7.87/2.68  tff(c_7908, plain, ('#skF_11'(k1_relat_1('#skF_13'), '#skF_13')=k1_xboole_0 | ~r2_hidden('#skF_11'(k1_relat_1('#skF_13'), '#skF_13'), k1_relat_1('#skF_13')) | k1_funct_1('#skF_13', '#skF_11'(k1_relat_1('#skF_13'), '#skF_13'))!=k1_xboole_0 | k6_relat_1(k1_relat_1('#skF_13'))='#skF_13' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_48, c_7877])).
% 7.87/2.68  tff(c_7931, plain, ('#skF_11'(k1_relat_1('#skF_13'), '#skF_13')=k1_xboole_0 | ~r2_hidden('#skF_11'(k1_relat_1('#skF_13'), '#skF_13'), k1_relat_1('#skF_13')) | k1_funct_1('#skF_13', '#skF_11'(k1_relat_1('#skF_13'), '#skF_13'))!=k1_xboole_0 | k6_relat_1(k1_relat_1('#skF_13'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_7908])).
% 7.87/2.68  tff(c_7932, plain, ('#skF_11'(k1_relat_1('#skF_13'), '#skF_13')=k1_xboole_0 | ~r2_hidden('#skF_11'(k1_relat_1('#skF_13'), '#skF_13'), k1_relat_1('#skF_13')) | k1_funct_1('#skF_13', '#skF_11'(k1_relat_1('#skF_13'), '#skF_13'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_7931])).
% 7.87/2.68  tff(c_8029, plain, (k1_funct_1('#skF_13', '#skF_11'(k1_relat_1('#skF_13'), '#skF_13'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7932])).
% 7.87/2.68  tff(c_7724, plain, (![C_384]: (k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_384))=k1_funct_1('#skF_13', C_384) | k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_384))=k1_xboole_0 | ~r2_hidden(C_384, k1_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_112, c_7679])).
% 7.87/2.68  tff(c_8031, plain, (![C_392]: (k1_funct_1('#skF_13', C_392)=C_392 | ~r2_hidden(C_392, k1_relat_1('#skF_13')) | k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_392))=k1_xboole_0 | ~r2_hidden(C_392, k1_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_7724, c_112])).
% 7.87/2.68  tff(c_8117, plain, (![C_393]: (k1_xboole_0=C_393 | ~r2_hidden(C_393, k1_relat_1('#skF_13')) | k1_funct_1('#skF_13', C_393)=C_393 | ~r2_hidden(C_393, k1_relat_1('#skF_13')) | ~r2_hidden(C_393, k1_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_8031, c_112])).
% 7.87/2.68  tff(c_8156, plain, (![B_103]: (k1_xboole_0=B_103 | k1_funct_1('#skF_13', B_103)=B_103 | ~r2_hidden(B_103, k1_relat_1('#skF_13')) | k1_funct_1('#skF_13', B_103)=k1_xboole_0 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_26, c_8117])).
% 7.87/2.68  tff(c_8181, plain, (![B_394]: (k1_xboole_0=B_394 | k1_funct_1('#skF_13', B_394)=B_394 | ~r2_hidden(B_394, k1_relat_1('#skF_13')) | k1_funct_1('#skF_13', B_394)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8156])).
% 7.87/2.68  tff(c_8234, plain, (![B_103]: (k1_xboole_0=B_103 | k1_funct_1('#skF_13', B_103)=B_103 | k1_funct_1('#skF_13', B_103)=k1_xboole_0 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_26, c_8181])).
% 7.87/2.68  tff(c_8271, plain, (![B_395]: (k1_xboole_0=B_395 | k1_funct_1('#skF_13', B_395)=B_395 | k1_funct_1('#skF_13', B_395)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8234])).
% 7.87/2.68  tff(c_46, plain, (![B_146]: (k1_funct_1(B_146, '#skF_11'(k1_relat_1(B_146), B_146))!='#skF_11'(k1_relat_1(B_146), B_146) | k6_relat_1(k1_relat_1(B_146))=B_146 | ~v1_funct_1(B_146) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.87/2.68  tff(c_8292, plain, (k6_relat_1(k1_relat_1('#skF_13'))='#skF_13' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | '#skF_11'(k1_relat_1('#skF_13'), '#skF_13')=k1_xboole_0 | k1_funct_1('#skF_13', '#skF_11'(k1_relat_1('#skF_13'), '#skF_13'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8271, c_46])).
% 7.87/2.68  tff(c_8359, plain, (k6_relat_1(k1_relat_1('#skF_13'))='#skF_13' | '#skF_11'(k1_relat_1('#skF_13'), '#skF_13')=k1_xboole_0 | k1_funct_1('#skF_13', '#skF_11'(k1_relat_1('#skF_13'), '#skF_13'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8292])).
% 7.87/2.68  tff(c_8360, plain, ('#skF_11'(k1_relat_1('#skF_13'), '#skF_13')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_8029, c_54, c_8359])).
% 7.87/2.68  tff(c_8381, plain, (k1_funct_1('#skF_13', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8360, c_8029])).
% 7.87/2.68  tff(c_8388, plain, (r2_hidden(k1_xboole_0, k1_relat_1('#skF_13')) | k6_relat_1(k1_relat_1('#skF_13'))='#skF_13' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_8360, c_48])).
% 7.87/2.68  tff(c_8395, plain, (r2_hidden(k1_xboole_0, k1_relat_1('#skF_13')) | k6_relat_1(k1_relat_1('#skF_13'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8388])).
% 7.87/2.68  tff(c_8396, plain, (r2_hidden(k1_xboole_0, k1_relat_1('#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_54, c_8395])).
% 7.87/2.68  tff(c_113, plain, (![A_164, C_165]: (r2_hidden('#skF_10'(A_164, k2_relat_1(A_164), C_165), k1_relat_1(A_164)) | ~r2_hidden(C_165, k2_relat_1(A_164)) | ~v1_funct_1(A_164) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.87/2.68  tff(c_116, plain, (![C_165]: (r2_hidden('#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_165), k1_relat_1('#skF_12')) | ~r2_hidden(C_165, k2_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_113])).
% 7.87/2.68  tff(c_118, plain, (![C_165]: (r2_hidden('#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_165), k1_relat_1('#skF_12')) | ~r2_hidden(C_165, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_116])).
% 7.87/2.68  tff(c_119, plain, (![C_166]: (k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_166))=C_166 | ~r2_hidden(C_166, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_106])).
% 7.87/2.68  tff(c_125, plain, (![C_166]: (r2_hidden(k4_tarski('#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_166), C_166), '#skF_12') | ~r2_hidden('#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_166), k1_relat_1('#skF_12')) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12') | ~r2_hidden(C_166, k1_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_119, c_22])).
% 7.87/2.68  tff(c_137, plain, (![C_166]: (r2_hidden(k4_tarski('#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_166), C_166), '#skF_12') | ~r2_hidden('#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_166), k1_relat_1('#skF_12')) | ~r2_hidden(C_166, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_125])).
% 7.87/2.68  tff(c_7339, plain, (![C_372]: ('#skF_1'('#skF_13', '#skF_12', '#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_372), k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_372)))=k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_372)) | ~r2_hidden(C_372, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_118, c_329])).
% 7.87/2.68  tff(c_7404, plain, (![C_375]: (k1_funct_1('#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_375))='#skF_1'('#skF_13', '#skF_12', '#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_375), C_375) | ~r2_hidden(C_375, k1_relat_1('#skF_13')) | ~r2_hidden(C_375, k1_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_112, c_7339])).
% 7.87/2.68  tff(c_7475, plain, (![C_376]: ('#skF_1'('#skF_13', '#skF_12', '#skF_12', '#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_376), C_376)=C_376 | ~r2_hidden(C_376, k1_relat_1('#skF_13')) | ~r2_hidden(C_376, k1_relat_1('#skF_13')) | ~r2_hidden(C_376, k1_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_7404, c_112])).
% 7.87/2.68  tff(c_7254, plain, (![D_365, E_366]: (r2_hidden(k4_tarski('#skF_1'('#skF_13', '#skF_12', '#skF_12', D_365, E_366), E_366), '#skF_13') | ~r2_hidden(k4_tarski(D_365, E_366), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_66, c_56, c_56, c_7242])).
% 7.87/2.68  tff(c_9237, plain, (![C_432]: (r2_hidden(k4_tarski(C_432, C_432), '#skF_13') | ~r2_hidden(k4_tarski('#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_432), C_432), '#skF_12') | ~r2_hidden(C_432, k1_relat_1('#skF_13')) | ~r2_hidden(C_432, k1_relat_1('#skF_13')) | ~r2_hidden(C_432, k1_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_7475, c_7254])).
% 7.87/2.68  tff(c_9242, plain, (![C_433]: (r2_hidden(k4_tarski(C_433, C_433), '#skF_13') | ~r2_hidden('#skF_10'('#skF_12', k1_relat_1('#skF_13'), C_433), k1_relat_1('#skF_12')) | ~r2_hidden(C_433, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_137, c_9237])).
% 7.87/2.68  tff(c_9252, plain, (![C_434]: (r2_hidden(k4_tarski(C_434, C_434), '#skF_13') | ~r2_hidden(C_434, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_118, c_9242])).
% 7.87/2.68  tff(c_9263, plain, (![C_434]: (k1_funct_1('#skF_13', C_434)=C_434 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden(C_434, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_9252, c_20])).
% 7.87/2.68  tff(c_9276, plain, (![C_435]: (k1_funct_1('#skF_13', C_435)=C_435 | ~r2_hidden(C_435, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_9263])).
% 7.87/2.68  tff(c_9282, plain, (k1_funct_1('#skF_13', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8396, c_9276])).
% 7.87/2.68  tff(c_9348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8381, c_9282])).
% 7.87/2.68  tff(c_9350, plain, (k1_funct_1('#skF_13', '#skF_11'(k1_relat_1('#skF_13'), '#skF_13'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_7932])).
% 7.87/2.68  tff(c_9358, plain, ('#skF_11'(k1_relat_1('#skF_13'), '#skF_13')!=k1_xboole_0 | k6_relat_1(k1_relat_1('#skF_13'))='#skF_13' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_9350, c_46])).
% 7.87/2.68  tff(c_9372, plain, ('#skF_11'(k1_relat_1('#skF_13'), '#skF_13')!=k1_xboole_0 | k6_relat_1(k1_relat_1('#skF_13'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_9358])).
% 7.87/2.68  tff(c_9373, plain, ('#skF_11'(k1_relat_1('#skF_13'), '#skF_13')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_9372])).
% 7.87/2.68  tff(c_9349, plain, (~r2_hidden('#skF_11'(k1_relat_1('#skF_13'), '#skF_13'), k1_relat_1('#skF_13')) | '#skF_11'(k1_relat_1('#skF_13'), '#skF_13')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7932])).
% 7.87/2.68  tff(c_9457, plain, (~r2_hidden('#skF_11'(k1_relat_1('#skF_13'), '#skF_13'), k1_relat_1('#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_9373, c_9349])).
% 7.87/2.68  tff(c_9460, plain, (k6_relat_1(k1_relat_1('#skF_13'))='#skF_13' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_48, c_9457])).
% 7.87/2.68  tff(c_9466, plain, (k6_relat_1(k1_relat_1('#skF_13'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_9460])).
% 7.87/2.68  tff(c_9468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_9466])).
% 7.87/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.87/2.68  
% 7.87/2.68  Inference rules
% 7.87/2.68  ----------------------
% 7.87/2.68  #Ref     : 3
% 7.87/2.68  #Sup     : 1959
% 7.87/2.68  #Fact    : 9
% 7.87/2.68  #Define  : 0
% 7.87/2.68  #Split   : 12
% 7.87/2.68  #Chain   : 0
% 7.87/2.68  #Close   : 0
% 7.87/2.68  
% 7.87/2.68  Ordering : KBO
% 7.87/2.68  
% 7.87/2.68  Simplification rules
% 7.87/2.68  ----------------------
% 7.87/2.68  #Subsume      : 329
% 7.87/2.68  #Demod        : 1558
% 7.87/2.68  #Tautology    : 380
% 7.87/2.68  #SimpNegUnit  : 76
% 7.87/2.68  #BackRed      : 4
% 7.87/2.68  
% 7.87/2.68  #Partial instantiations: 0
% 7.87/2.68  #Strategies tried      : 1
% 7.87/2.68  
% 7.87/2.68  Timing (in seconds)
% 7.87/2.68  ----------------------
% 7.87/2.69  Preprocessing        : 0.37
% 7.87/2.69  Parsing              : 0.18
% 7.87/2.69  CNF conversion       : 0.04
% 7.87/2.69  Main loop            : 1.51
% 7.87/2.69  Inferencing          : 0.51
% 7.87/2.69  Reduction            : 0.46
% 7.87/2.69  Demodulation         : 0.31
% 7.87/2.69  BG Simplification    : 0.08
% 7.87/2.69  Subsumption          : 0.33
% 7.87/2.69  Abstraction          : 0.12
% 7.87/2.69  MUC search           : 0.00
% 7.87/2.69  Cooper               : 0.00
% 7.87/2.69  Total                : 1.92
% 7.87/2.69  Index Insertion      : 0.00
% 7.87/2.69  Index Deletion       : 0.00
% 7.87/2.69  Index Matching       : 0.00
% 7.87/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
