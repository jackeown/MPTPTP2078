%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:15 EST 2020

% Result     : Theorem 8.13s
% Output     : CNFRefutation 8.13s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 154 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  127 ( 316 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_60,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_62,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_44,plain,(
    ! [A_19] : r2_hidden(A_19,k1_ordinal1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_54,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_56,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | r1_ordinal1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_114,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_62])).

tff(c_42,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r1_ordinal1(A_17,B_18)
      | ~ v3_ordinal1(B_18)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_65,plain,(
    ! [A_31] :
      ( v1_ordinal1(A_31)
      | ~ v3_ordinal1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_73,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_65])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r2_xboole_0(A_9,B_10)
      | B_10 = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_456,plain,(
    ! [A_85,B_86] :
      ( r2_hidden(A_85,B_86)
      | ~ r2_xboole_0(A_85,B_86)
      | ~ v3_ordinal1(B_86)
      | ~ v1_ordinal1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2728,plain,(
    ! [A_262,B_263] :
      ( r2_hidden(A_262,B_263)
      | ~ v3_ordinal1(B_263)
      | ~ v1_ordinal1(A_262)
      | B_263 = A_262
      | ~ r1_tarski(A_262,B_263) ) ),
    inference(resolution,[status(thm)],[c_22,c_456])).

tff(c_38,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_tarski(A_16)) = k1_ordinal1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_139,plain,(
    ! [D_50,A_51,B_52] :
      ( ~ r2_hidden(D_50,A_51)
      | r2_hidden(D_50,k2_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_175,plain,(
    ! [D_56,A_57] :
      ( ~ r2_hidden(D_56,A_57)
      | r2_hidden(D_56,k1_ordinal1(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_139])).

tff(c_206,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_175,c_83])).

tff(c_3029,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_2728,c_206])).

tff(c_3145,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_52,c_3029])).

tff(c_3157,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3145])).

tff(c_3160,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_3157])).

tff(c_3164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_114,c_3160])).

tff(c_3165,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3145])).

tff(c_3170,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3165,c_83])).

tff(c_3176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3170])).

tff(c_3177,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3179,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_3180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3177,c_3179])).

tff(c_3181,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_3815,plain,(
    ! [D_341,B_342,A_343] :
      ( r2_hidden(D_341,B_342)
      | r2_hidden(D_341,A_343)
      | ~ r2_hidden(D_341,k2_xboole_0(A_343,B_342)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5037,plain,(
    ! [D_445,A_446] :
      ( r2_hidden(D_445,k1_tarski(A_446))
      | r2_hidden(D_445,A_446)
      | ~ r2_hidden(D_445,k1_ordinal1(A_446)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3815])).

tff(c_32,plain,(
    ! [A_14] : k3_tarski(k1_tarski(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3230,plain,(
    ! [A_275,B_276] :
      ( r1_tarski(A_275,k3_tarski(B_276))
      | ~ r2_hidden(A_275,B_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3237,plain,(
    ! [A_275,A_14] :
      ( r1_tarski(A_275,A_14)
      | ~ r2_hidden(A_275,k1_tarski(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3230])).

tff(c_10048,plain,(
    ! [D_706,A_707] :
      ( r1_tarski(D_706,A_707)
      | r2_hidden(D_706,A_707)
      | ~ r2_hidden(D_706,k1_ordinal1(A_707)) ) ),
    inference(resolution,[status(thm)],[c_5037,c_3237])).

tff(c_10129,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_3181,c_10048])).

tff(c_10131,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10129])).

tff(c_3585,plain,(
    ! [B_322,A_323] :
      ( r2_hidden(B_322,A_323)
      | r1_ordinal1(A_323,B_322)
      | ~ v3_ordinal1(B_322)
      | ~ v3_ordinal1(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3695,plain,(
    ! [A_323,B_322] :
      ( ~ r2_hidden(A_323,B_322)
      | r1_ordinal1(A_323,B_322)
      | ~ v3_ordinal1(B_322)
      | ~ v3_ordinal1(A_323) ) ),
    inference(resolution,[status(thm)],[c_3585,c_2])).

tff(c_10134,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10131,c_3695])).

tff(c_10142,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_10134])).

tff(c_10144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3177,c_10142])).

tff(c_10145,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_10129])).

tff(c_40,plain,(
    ! [A_17,B_18] :
      ( r1_ordinal1(A_17,B_18)
      | ~ r1_tarski(A_17,B_18)
      | ~ v3_ordinal1(B_18)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10149,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10145,c_40])).

tff(c_10152,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_10149])).

tff(c_10154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3177,c_10152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:47:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.13/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.13/2.81  
% 8.13/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.13/2.81  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 8.13/2.81  
% 8.13/2.81  %Foreground sorts:
% 8.13/2.81  
% 8.13/2.81  
% 8.13/2.81  %Background operators:
% 8.13/2.81  
% 8.13/2.81  
% 8.13/2.81  %Foreground operators:
% 8.13/2.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.13/2.81  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 8.13/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.13/2.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.13/2.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.13/2.81  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 8.13/2.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.13/2.81  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 8.13/2.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.13/2.81  tff('#skF_3', type, '#skF_3': $i).
% 8.13/2.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.13/2.81  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 8.13/2.81  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 8.13/2.81  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 8.13/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.13/2.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.13/2.81  tff('#skF_4', type, '#skF_4': $i).
% 8.13/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.13/2.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.13/2.81  
% 8.13/2.83  tff(f_72, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 8.13/2.83  tff(f_105, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 8.13/2.83  tff(f_70, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 8.13/2.83  tff(f_60, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 8.13/2.83  tff(f_46, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 8.13/2.83  tff(f_81, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 8.13/2.83  tff(f_62, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 8.13/2.83  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 8.13/2.83  tff(f_54, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 8.13/2.83  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 8.13/2.83  tff(f_90, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 8.13/2.83  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 8.13/2.83  tff(c_44, plain, (![A_19]: (r2_hidden(A_19, k1_ordinal1(A_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.13/2.83  tff(c_54, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.13/2.83  tff(c_52, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.13/2.83  tff(c_56, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.13/2.83  tff(c_83, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitLeft, [status(thm)], [c_56])).
% 8.13/2.83  tff(c_62, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | r1_ordinal1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.13/2.83  tff(c_114, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_83, c_62])).
% 8.13/2.83  tff(c_42, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r1_ordinal1(A_17, B_18) | ~v3_ordinal1(B_18) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.13/2.83  tff(c_65, plain, (![A_31]: (v1_ordinal1(A_31) | ~v3_ordinal1(A_31))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.13/2.83  tff(c_73, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_65])).
% 8.13/2.83  tff(c_22, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.13/2.83  tff(c_456, plain, (![A_85, B_86]: (r2_hidden(A_85, B_86) | ~r2_xboole_0(A_85, B_86) | ~v3_ordinal1(B_86) | ~v1_ordinal1(A_85))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.13/2.83  tff(c_2728, plain, (![A_262, B_263]: (r2_hidden(A_262, B_263) | ~v3_ordinal1(B_263) | ~v1_ordinal1(A_262) | B_263=A_262 | ~r1_tarski(A_262, B_263))), inference(resolution, [status(thm)], [c_22, c_456])).
% 8.13/2.83  tff(c_38, plain, (![A_16]: (k2_xboole_0(A_16, k1_tarski(A_16))=k1_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.13/2.83  tff(c_139, plain, (![D_50, A_51, B_52]: (~r2_hidden(D_50, A_51) | r2_hidden(D_50, k2_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.13/2.83  tff(c_175, plain, (![D_56, A_57]: (~r2_hidden(D_56, A_57) | r2_hidden(D_56, k1_ordinal1(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_139])).
% 8.13/2.83  tff(c_206, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_175, c_83])).
% 8.13/2.83  tff(c_3029, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1('#skF_3') | '#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_2728, c_206])).
% 8.13/2.83  tff(c_3145, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_52, c_3029])).
% 8.13/2.83  tff(c_3157, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_3145])).
% 8.13/2.83  tff(c_3160, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_3157])).
% 8.13/2.83  tff(c_3164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_114, c_3160])).
% 8.13/2.83  tff(c_3165, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_3145])).
% 8.13/2.83  tff(c_3170, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3165, c_83])).
% 8.13/2.83  tff(c_3176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_3170])).
% 8.13/2.83  tff(c_3177, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 8.13/2.83  tff(c_3179, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 8.13/2.83  tff(c_3180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3177, c_3179])).
% 8.13/2.83  tff(c_3181, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_62])).
% 8.13/2.83  tff(c_3815, plain, (![D_341, B_342, A_343]: (r2_hidden(D_341, B_342) | r2_hidden(D_341, A_343) | ~r2_hidden(D_341, k2_xboole_0(A_343, B_342)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.13/2.83  tff(c_5037, plain, (![D_445, A_446]: (r2_hidden(D_445, k1_tarski(A_446)) | r2_hidden(D_445, A_446) | ~r2_hidden(D_445, k1_ordinal1(A_446)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3815])).
% 8.13/2.83  tff(c_32, plain, (![A_14]: (k3_tarski(k1_tarski(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.13/2.83  tff(c_3230, plain, (![A_275, B_276]: (r1_tarski(A_275, k3_tarski(B_276)) | ~r2_hidden(A_275, B_276))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.13/2.83  tff(c_3237, plain, (![A_275, A_14]: (r1_tarski(A_275, A_14) | ~r2_hidden(A_275, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3230])).
% 8.13/2.83  tff(c_10048, plain, (![D_706, A_707]: (r1_tarski(D_706, A_707) | r2_hidden(D_706, A_707) | ~r2_hidden(D_706, k1_ordinal1(A_707)))), inference(resolution, [status(thm)], [c_5037, c_3237])).
% 8.13/2.83  tff(c_10129, plain, (r1_tarski('#skF_3', '#skF_4') | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_3181, c_10048])).
% 8.13/2.83  tff(c_10131, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_10129])).
% 8.13/2.83  tff(c_3585, plain, (![B_322, A_323]: (r2_hidden(B_322, A_323) | r1_ordinal1(A_323, B_322) | ~v3_ordinal1(B_322) | ~v3_ordinal1(A_323))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.13/2.83  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 8.13/2.83  tff(c_3695, plain, (![A_323, B_322]: (~r2_hidden(A_323, B_322) | r1_ordinal1(A_323, B_322) | ~v3_ordinal1(B_322) | ~v3_ordinal1(A_323))), inference(resolution, [status(thm)], [c_3585, c_2])).
% 8.13/2.83  tff(c_10134, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_10131, c_3695])).
% 8.13/2.83  tff(c_10142, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_10134])).
% 8.13/2.83  tff(c_10144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3177, c_10142])).
% 8.13/2.83  tff(c_10145, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_10129])).
% 8.13/2.83  tff(c_40, plain, (![A_17, B_18]: (r1_ordinal1(A_17, B_18) | ~r1_tarski(A_17, B_18) | ~v3_ordinal1(B_18) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.13/2.83  tff(c_10149, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_10145, c_40])).
% 8.13/2.83  tff(c_10152, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_10149])).
% 8.13/2.83  tff(c_10154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3177, c_10152])).
% 8.13/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.13/2.83  
% 8.13/2.83  Inference rules
% 8.13/2.83  ----------------------
% 8.13/2.83  #Ref     : 0
% 8.13/2.83  #Sup     : 2111
% 8.13/2.83  #Fact    : 14
% 8.13/2.83  #Define  : 0
% 8.13/2.83  #Split   : 6
% 8.13/2.83  #Chain   : 0
% 8.13/2.83  #Close   : 0
% 8.13/2.83  
% 8.13/2.83  Ordering : KBO
% 8.13/2.83  
% 8.13/2.83  Simplification rules
% 8.13/2.83  ----------------------
% 8.13/2.83  #Subsume      : 354
% 8.13/2.83  #Demod        : 72
% 8.13/2.83  #Tautology    : 69
% 8.13/2.83  #SimpNegUnit  : 42
% 8.13/2.83  #BackRed      : 9
% 8.13/2.83  
% 8.13/2.83  #Partial instantiations: 0
% 8.13/2.83  #Strategies tried      : 1
% 8.13/2.83  
% 8.13/2.83  Timing (in seconds)
% 8.13/2.83  ----------------------
% 8.13/2.83  Preprocessing        : 0.30
% 8.13/2.83  Parsing              : 0.15
% 8.13/2.83  CNF conversion       : 0.02
% 8.13/2.83  Main loop            : 1.69
% 8.13/2.83  Inferencing          : 0.47
% 8.13/2.83  Reduction            : 0.44
% 8.13/2.83  Demodulation         : 0.25
% 8.13/2.83  BG Simplification    : 0.06
% 8.13/2.83  Subsumption          : 0.54
% 8.13/2.83  Abstraction          : 0.07
% 8.13/2.83  MUC search           : 0.00
% 8.13/2.83  Cooper               : 0.00
% 8.13/2.83  Total                : 2.02
% 8.13/2.83  Index Insertion      : 0.00
% 8.13/2.83  Index Deletion       : 0.00
% 8.13/2.83  Index Matching       : 0.00
% 8.13/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
