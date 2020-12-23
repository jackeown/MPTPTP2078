%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:52 EST 2020

% Result     : Theorem 5.47s
% Output     : CNFRefutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :   58 (  78 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  159 ( 249 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B)
              & v5_funct_1(B,A) )
           => r1_tarski(k1_relat_1(B),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_86,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    v5_funct_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_1'(A_35,B_36),A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_35] : r1_tarski(A_35,A_35) ),
    inference(resolution,[status(thm)],[c_45,c_4])).

tff(c_104,plain,(
    ! [A_52,B_53] :
      ( k1_funct_1(A_52,B_53) = k1_xboole_0
      | r2_hidden(B_53,k1_relat_1(A_52))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_112,plain,(
    ! [A_1,A_52] :
      ( r1_tarski(A_1,k1_relat_1(A_52))
      | k1_funct_1(A_52,'#skF_1'(A_1,k1_relat_1(A_52))) = k1_xboole_0
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_16,plain,(
    ! [B_18,C_21,A_12] :
      ( r2_hidden(k1_funct_1(B_18,C_21),k1_funct_1(A_12,C_21))
      | ~ r2_hidden(C_21,k1_relat_1(B_18))
      | ~ v5_funct_1(B_18,A_12)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_323,plain,(
    ! [B_99,C_100,A_101] :
      ( r2_hidden(k1_funct_1(B_99,C_100),k1_funct_1(A_101,C_100))
      | ~ r2_hidden(C_100,k1_relat_1(B_99))
      | ~ v5_funct_1(B_99,A_101)
      | ~ v1_funct_1(B_99)
      | ~ v1_relat_1(B_99)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [C_45,B_46,A_47] :
      ( r2_hidden(C_45,B_46)
      | ~ r2_hidden(C_45,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [A_60,B_61,B_62] :
      ( r2_hidden('#skF_2'(A_60,B_61),B_62)
      | ~ r1_tarski(B_61,B_62)
      | r1_xboole_0(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,B_39)
      | ~ r2_hidden(C_40,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    ! [C_40,A_11] :
      ( ~ r2_hidden(C_40,k1_xboole_0)
      | ~ r2_hidden(C_40,A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_52])).

tff(c_245,plain,(
    ! [A_83,B_84,A_85] :
      ( ~ r2_hidden('#skF_2'(A_83,B_84),A_85)
      | ~ r1_tarski(B_84,k1_xboole_0)
      | r1_xboole_0(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_135,c_55])).

tff(c_267,plain,(
    ! [B_86,A_87] :
      ( ~ r1_tarski(B_86,k1_xboole_0)
      | r1_xboole_0(A_87,B_86) ) ),
    inference(resolution,[status(thm)],[c_12,c_245])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_270,plain,(
    ! [C_10,B_86,A_87] :
      ( ~ r2_hidden(C_10,B_86)
      | ~ r2_hidden(C_10,A_87)
      | ~ r1_tarski(B_86,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_267,c_8])).

tff(c_1201,plain,(
    ! [B_248,C_249,A_250,A_251] :
      ( ~ r2_hidden(k1_funct_1(B_248,C_249),A_250)
      | ~ r1_tarski(k1_funct_1(A_251,C_249),k1_xboole_0)
      | ~ r2_hidden(C_249,k1_relat_1(B_248))
      | ~ v5_funct_1(B_248,A_251)
      | ~ v1_funct_1(B_248)
      | ~ v1_relat_1(B_248)
      | ~ v1_funct_1(A_251)
      | ~ v1_relat_1(A_251) ) ),
    inference(resolution,[status(thm)],[c_323,c_270])).

tff(c_1296,plain,(
    ! [A_263,C_264,B_265,A_266] :
      ( ~ r1_tarski(k1_funct_1(A_263,C_264),k1_xboole_0)
      | ~ v5_funct_1(B_265,A_263)
      | ~ v1_funct_1(A_263)
      | ~ v1_relat_1(A_263)
      | ~ r2_hidden(C_264,k1_relat_1(B_265))
      | ~ v5_funct_1(B_265,A_266)
      | ~ v1_funct_1(B_265)
      | ~ v1_relat_1(B_265)
      | ~ v1_funct_1(A_266)
      | ~ v1_relat_1(A_266) ) ),
    inference(resolution,[status(thm)],[c_16,c_1201])).

tff(c_1300,plain,(
    ! [B_265,A_52,A_1,A_266] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ v5_funct_1(B_265,A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52)
      | ~ r2_hidden('#skF_1'(A_1,k1_relat_1(A_52)),k1_relat_1(B_265))
      | ~ v5_funct_1(B_265,A_266)
      | ~ v1_funct_1(B_265)
      | ~ v1_relat_1(B_265)
      | ~ v1_funct_1(A_266)
      | ~ v1_relat_1(A_266)
      | r1_tarski(A_1,k1_relat_1(A_52))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1296])).

tff(c_1485,plain,(
    ! [B_291,A_292,A_293,A_294] :
      ( ~ v5_funct_1(B_291,A_292)
      | ~ r2_hidden('#skF_1'(A_293,k1_relat_1(A_292)),k1_relat_1(B_291))
      | ~ v5_funct_1(B_291,A_294)
      | ~ v1_funct_1(B_291)
      | ~ v1_relat_1(B_291)
      | ~ v1_funct_1(A_294)
      | ~ v1_relat_1(A_294)
      | r1_tarski(A_293,k1_relat_1(A_292))
      | ~ v1_funct_1(A_292)
      | ~ v1_relat_1(A_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1300])).

tff(c_1498,plain,(
    ! [B_295,A_296,A_297] :
      ( ~ v5_funct_1(B_295,A_296)
      | ~ v5_funct_1(B_295,A_297)
      | ~ v1_funct_1(B_295)
      | ~ v1_relat_1(B_295)
      | ~ v1_funct_1(A_297)
      | ~ v1_relat_1(A_297)
      | ~ v1_funct_1(A_296)
      | ~ v1_relat_1(A_296)
      | r1_tarski(k1_relat_1(B_295),k1_relat_1(A_296)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1485])).

tff(c_1504,plain,(
    ! [A_296] :
      ( ~ v5_funct_1('#skF_5',A_296)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_funct_1(A_296)
      | ~ v1_relat_1(A_296)
      | r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(A_296)) ) ),
    inference(resolution,[status(thm)],[c_32,c_1498])).

tff(c_1510,plain,(
    ! [A_298] :
      ( ~ v5_funct_1('#skF_5',A_298)
      | ~ v1_funct_1(A_298)
      | ~ v1_relat_1(A_298)
      | r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(A_298)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_1504])).

tff(c_30,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1557,plain,
    ( ~ v5_funct_1('#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1510,c_30])).

tff(c_1586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_1557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.47/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.47/2.17  
% 5.47/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.47/2.18  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 5.47/2.18  
% 5.47/2.18  %Foreground sorts:
% 5.47/2.18  
% 5.47/2.18  
% 5.47/2.18  %Background operators:
% 5.47/2.18  
% 5.47/2.18  
% 5.47/2.18  %Foreground operators:
% 5.47/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.47/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.47/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.47/2.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.47/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.47/2.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.47/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.47/2.18  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 5.47/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.47/2.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.47/2.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.47/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.47/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.47/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.47/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.47/2.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.47/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.47/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.47/2.18  
% 5.47/2.19  tff(f_100, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (((v1_relat_1(B) & v1_funct_1(B)) & v5_funct_1(B, A)) => r1_tarski(k1_relat_1(B), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_1)).
% 5.47/2.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.47/2.19  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 5.47/2.19  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 5.47/2.19  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.47/2.19  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.47/2.19  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.47/2.19  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.47/2.19  tff(c_32, plain, (v5_funct_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.47/2.19  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.47/2.19  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.47/2.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.47/2.19  tff(c_45, plain, (![A_35, B_36]: (r2_hidden('#skF_1'(A_35, B_36), A_35) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.47/2.19  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.47/2.19  tff(c_50, plain, (![A_35]: (r1_tarski(A_35, A_35))), inference(resolution, [status(thm)], [c_45, c_4])).
% 5.47/2.19  tff(c_104, plain, (![A_52, B_53]: (k1_funct_1(A_52, B_53)=k1_xboole_0 | r2_hidden(B_53, k1_relat_1(A_52)) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.47/2.19  tff(c_112, plain, (![A_1, A_52]: (r1_tarski(A_1, k1_relat_1(A_52)) | k1_funct_1(A_52, '#skF_1'(A_1, k1_relat_1(A_52)))=k1_xboole_0 | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(resolution, [status(thm)], [c_104, c_4])).
% 5.47/2.19  tff(c_16, plain, (![B_18, C_21, A_12]: (r2_hidden(k1_funct_1(B_18, C_21), k1_funct_1(A_12, C_21)) | ~r2_hidden(C_21, k1_relat_1(B_18)) | ~v5_funct_1(B_18, A_12) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.47/2.19  tff(c_323, plain, (![B_99, C_100, A_101]: (r2_hidden(k1_funct_1(B_99, C_100), k1_funct_1(A_101, C_100)) | ~r2_hidden(C_100, k1_relat_1(B_99)) | ~v5_funct_1(B_99, A_101) | ~v1_funct_1(B_99) | ~v1_relat_1(B_99) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.47/2.19  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.47/2.19  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.47/2.19  tff(c_76, plain, (![C_45, B_46, A_47]: (r2_hidden(C_45, B_46) | ~r2_hidden(C_45, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.47/2.19  tff(c_135, plain, (![A_60, B_61, B_62]: (r2_hidden('#skF_2'(A_60, B_61), B_62) | ~r1_tarski(B_61, B_62) | r1_xboole_0(A_60, B_61))), inference(resolution, [status(thm)], [c_10, c_76])).
% 5.47/2.19  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.47/2.19  tff(c_52, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, B_39) | ~r2_hidden(C_40, A_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.47/2.19  tff(c_55, plain, (![C_40, A_11]: (~r2_hidden(C_40, k1_xboole_0) | ~r2_hidden(C_40, A_11))), inference(resolution, [status(thm)], [c_14, c_52])).
% 5.47/2.19  tff(c_245, plain, (![A_83, B_84, A_85]: (~r2_hidden('#skF_2'(A_83, B_84), A_85) | ~r1_tarski(B_84, k1_xboole_0) | r1_xboole_0(A_83, B_84))), inference(resolution, [status(thm)], [c_135, c_55])).
% 5.47/2.19  tff(c_267, plain, (![B_86, A_87]: (~r1_tarski(B_86, k1_xboole_0) | r1_xboole_0(A_87, B_86))), inference(resolution, [status(thm)], [c_12, c_245])).
% 5.47/2.19  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.47/2.19  tff(c_270, plain, (![C_10, B_86, A_87]: (~r2_hidden(C_10, B_86) | ~r2_hidden(C_10, A_87) | ~r1_tarski(B_86, k1_xboole_0))), inference(resolution, [status(thm)], [c_267, c_8])).
% 5.47/2.19  tff(c_1201, plain, (![B_248, C_249, A_250, A_251]: (~r2_hidden(k1_funct_1(B_248, C_249), A_250) | ~r1_tarski(k1_funct_1(A_251, C_249), k1_xboole_0) | ~r2_hidden(C_249, k1_relat_1(B_248)) | ~v5_funct_1(B_248, A_251) | ~v1_funct_1(B_248) | ~v1_relat_1(B_248) | ~v1_funct_1(A_251) | ~v1_relat_1(A_251))), inference(resolution, [status(thm)], [c_323, c_270])).
% 5.47/2.19  tff(c_1296, plain, (![A_263, C_264, B_265, A_266]: (~r1_tarski(k1_funct_1(A_263, C_264), k1_xboole_0) | ~v5_funct_1(B_265, A_263) | ~v1_funct_1(A_263) | ~v1_relat_1(A_263) | ~r2_hidden(C_264, k1_relat_1(B_265)) | ~v5_funct_1(B_265, A_266) | ~v1_funct_1(B_265) | ~v1_relat_1(B_265) | ~v1_funct_1(A_266) | ~v1_relat_1(A_266))), inference(resolution, [status(thm)], [c_16, c_1201])).
% 5.47/2.19  tff(c_1300, plain, (![B_265, A_52, A_1, A_266]: (~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v5_funct_1(B_265, A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52) | ~r2_hidden('#skF_1'(A_1, k1_relat_1(A_52)), k1_relat_1(B_265)) | ~v5_funct_1(B_265, A_266) | ~v1_funct_1(B_265) | ~v1_relat_1(B_265) | ~v1_funct_1(A_266) | ~v1_relat_1(A_266) | r1_tarski(A_1, k1_relat_1(A_52)) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1296])).
% 5.47/2.19  tff(c_1485, plain, (![B_291, A_292, A_293, A_294]: (~v5_funct_1(B_291, A_292) | ~r2_hidden('#skF_1'(A_293, k1_relat_1(A_292)), k1_relat_1(B_291)) | ~v5_funct_1(B_291, A_294) | ~v1_funct_1(B_291) | ~v1_relat_1(B_291) | ~v1_funct_1(A_294) | ~v1_relat_1(A_294) | r1_tarski(A_293, k1_relat_1(A_292)) | ~v1_funct_1(A_292) | ~v1_relat_1(A_292))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1300])).
% 5.47/2.19  tff(c_1498, plain, (![B_295, A_296, A_297]: (~v5_funct_1(B_295, A_296) | ~v5_funct_1(B_295, A_297) | ~v1_funct_1(B_295) | ~v1_relat_1(B_295) | ~v1_funct_1(A_297) | ~v1_relat_1(A_297) | ~v1_funct_1(A_296) | ~v1_relat_1(A_296) | r1_tarski(k1_relat_1(B_295), k1_relat_1(A_296)))), inference(resolution, [status(thm)], [c_6, c_1485])).
% 5.47/2.19  tff(c_1504, plain, (![A_296]: (~v5_funct_1('#skF_5', A_296) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(A_296) | ~v1_relat_1(A_296) | r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(A_296)))), inference(resolution, [status(thm)], [c_32, c_1498])).
% 5.47/2.19  tff(c_1510, plain, (![A_298]: (~v5_funct_1('#skF_5', A_298) | ~v1_funct_1(A_298) | ~v1_relat_1(A_298) | r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(A_298)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_1504])).
% 5.47/2.19  tff(c_30, plain, (~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.47/2.19  tff(c_1557, plain, (~v5_funct_1('#skF_5', '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1510, c_30])).
% 5.47/2.19  tff(c_1586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_1557])).
% 5.47/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.47/2.19  
% 5.47/2.19  Inference rules
% 5.47/2.19  ----------------------
% 5.47/2.19  #Ref     : 0
% 5.47/2.19  #Sup     : 379
% 5.47/2.19  #Fact    : 0
% 5.47/2.19  #Define  : 0
% 5.47/2.19  #Split   : 1
% 5.47/2.19  #Chain   : 0
% 5.47/2.19  #Close   : 0
% 5.47/2.19  
% 5.47/2.19  Ordering : KBO
% 5.47/2.19  
% 5.47/2.19  Simplification rules
% 5.47/2.19  ----------------------
% 5.47/2.19  #Subsume      : 193
% 5.47/2.19  #Demod        : 35
% 5.47/2.19  #Tautology    : 22
% 5.47/2.19  #SimpNegUnit  : 0
% 5.47/2.19  #BackRed      : 0
% 5.47/2.19  
% 5.47/2.19  #Partial instantiations: 0
% 5.47/2.19  #Strategies tried      : 1
% 5.47/2.19  
% 5.47/2.19  Timing (in seconds)
% 5.47/2.19  ----------------------
% 5.47/2.19  Preprocessing        : 0.41
% 5.47/2.19  Parsing              : 0.22
% 5.47/2.19  CNF conversion       : 0.04
% 5.47/2.19  Main loop            : 0.94
% 5.47/2.19  Inferencing          : 0.27
% 5.47/2.19  Reduction            : 0.18
% 5.47/2.19  Demodulation         : 0.12
% 5.47/2.19  BG Simplification    : 0.04
% 5.47/2.19  Subsumption          : 0.40
% 5.47/2.19  Abstraction          : 0.04
% 5.47/2.19  MUC search           : 0.00
% 5.47/2.19  Cooper               : 0.00
% 5.47/2.19  Total                : 1.38
% 5.47/2.19  Index Insertion      : 0.00
% 5.47/2.19  Index Deletion       : 0.00
% 5.47/2.19  Index Matching       : 0.00
% 5.47/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
