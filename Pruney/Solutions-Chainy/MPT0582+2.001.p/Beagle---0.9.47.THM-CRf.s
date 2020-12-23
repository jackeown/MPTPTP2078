%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:58 EST 2020

% Result     : Theorem 20.33s
% Output     : CNFRefutation 20.36s
% Verified   : 
% Statistics : Number of formulae       :   58 (  75 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  103 ( 164 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( ( r1_tarski(k1_relat_1(C),A)
                & r1_tarski(C,B) )
             => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_61,B_62] :
      ( v1_relat_1(k7_relat_1(A_61,B_62))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    r1_tarski('#skF_14','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_57,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68,B_69),A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_68] : r1_tarski(A_68,A_68) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_50,plain,(
    r1_tarski(k1_relat_1('#skF_14'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_90,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(k4_tarski('#skF_6'(A_84,B_85),'#skF_7'(A_84,B_85)),A_84)
      | r1_tarski(A_84,B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    ! [C_57,A_42,D_60] :
      ( r2_hidden(C_57,k1_relat_1(A_42))
      | ~ r2_hidden(k4_tarski(C_57,D_60),A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_105,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_6'(A_88,B_89),k1_relat_1(A_88))
      | r1_tarski(A_88,B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_90,c_34])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [A_100,B_101,B_102] :
      ( r2_hidden('#skF_6'(A_100,B_101),B_102)
      | ~ r1_tarski(k1_relat_1(A_100),B_102)
      | r1_tarski(A_100,B_101)
      | ~ v1_relat_1(A_100) ) ),
    inference(resolution,[status(thm)],[c_105,c_2])).

tff(c_2154,plain,(
    ! [A_243,B_244,B_245,B_246] :
      ( r2_hidden('#skF_6'(A_243,B_244),B_245)
      | ~ r1_tarski(B_246,B_245)
      | ~ r1_tarski(k1_relat_1(A_243),B_246)
      | r1_tarski(A_243,B_244)
      | ~ v1_relat_1(A_243) ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_2186,plain,(
    ! [A_249,B_250] :
      ( r2_hidden('#skF_6'(A_249,B_250),'#skF_12')
      | ~ r1_tarski(k1_relat_1(A_249),k1_relat_1('#skF_14'))
      | r1_tarski(A_249,B_250)
      | ~ v1_relat_1(A_249) ) ),
    inference(resolution,[status(thm)],[c_50,c_2154])).

tff(c_2195,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_6'('#skF_14',B_250),'#skF_12')
      | r1_tarski('#skF_14',B_250)
      | ~ v1_relat_1('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_62,c_2186])).

tff(c_2202,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_6'('#skF_14',B_250),'#skF_12')
      | r1_tarski('#skF_14',B_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2195])).

tff(c_97,plain,(
    ! [A_84,B_85,B_2] :
      ( r2_hidden(k4_tarski('#skF_6'(A_84,B_85),'#skF_7'(A_84,B_85)),B_2)
      | ~ r1_tarski(A_84,B_2)
      | r1_tarski(A_84,B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_881,plain,(
    ! [D_165,E_166,A_167,B_168] :
      ( r2_hidden(k4_tarski(D_165,E_166),k7_relat_1(A_167,B_168))
      | ~ r2_hidden(k4_tarski(D_165,E_166),A_167)
      | ~ r2_hidden(D_165,B_168)
      | ~ v1_relat_1(k7_relat_1(A_167,B_168))
      | ~ v1_relat_1(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_25,B_35] :
      ( ~ r2_hidden(k4_tarski('#skF_6'(A_25,B_35),'#skF_7'(A_25,B_35)),B_35)
      | r1_tarski(A_25,B_35)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_13686,plain,(
    ! [A_552,A_553,B_554] :
      ( r1_tarski(A_552,k7_relat_1(A_553,B_554))
      | ~ v1_relat_1(A_552)
      | ~ r2_hidden(k4_tarski('#skF_6'(A_552,k7_relat_1(A_553,B_554)),'#skF_7'(A_552,k7_relat_1(A_553,B_554))),A_553)
      | ~ r2_hidden('#skF_6'(A_552,k7_relat_1(A_553,B_554)),B_554)
      | ~ v1_relat_1(k7_relat_1(A_553,B_554))
      | ~ v1_relat_1(A_553) ) ),
    inference(resolution,[status(thm)],[c_881,c_28])).

tff(c_43936,plain,(
    ! [A_948,B_949,B_950] :
      ( ~ r2_hidden('#skF_6'(A_948,k7_relat_1(B_949,B_950)),B_950)
      | ~ v1_relat_1(k7_relat_1(B_949,B_950))
      | ~ v1_relat_1(B_949)
      | ~ r1_tarski(A_948,B_949)
      | r1_tarski(A_948,k7_relat_1(B_949,B_950))
      | ~ v1_relat_1(A_948) ) ),
    inference(resolution,[status(thm)],[c_97,c_13686])).

tff(c_44057,plain,(
    ! [B_949] :
      ( ~ v1_relat_1(k7_relat_1(B_949,'#skF_12'))
      | ~ v1_relat_1(B_949)
      | ~ r1_tarski('#skF_14',B_949)
      | ~ v1_relat_1('#skF_14')
      | r1_tarski('#skF_14',k7_relat_1(B_949,'#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_2202,c_43936])).

tff(c_44170,plain,(
    ! [B_951] :
      ( ~ v1_relat_1(k7_relat_1(B_951,'#skF_12'))
      | ~ v1_relat_1(B_951)
      | ~ r1_tarski('#skF_14',B_951)
      | r1_tarski('#skF_14',k7_relat_1(B_951,'#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44057])).

tff(c_46,plain,(
    ~ r1_tarski('#skF_14',k7_relat_1('#skF_13','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44224,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_13','#skF_12'))
    | ~ v1_relat_1('#skF_13')
    | ~ r1_tarski('#skF_14','#skF_13') ),
    inference(resolution,[status(thm)],[c_44170,c_46])).

tff(c_44259,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_13','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_54,c_44224])).

tff(c_44264,plain,(
    ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_44,c_44259])).

tff(c_44268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:45 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.33/10.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.33/10.40  
% 20.33/10.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.33/10.41  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_12
% 20.33/10.41  
% 20.33/10.41  %Foreground sorts:
% 20.33/10.41  
% 20.33/10.41  
% 20.33/10.41  %Background operators:
% 20.33/10.41  
% 20.33/10.41  
% 20.33/10.41  %Foreground operators:
% 20.33/10.41  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 20.33/10.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.33/10.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.33/10.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 20.33/10.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 20.33/10.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 20.33/10.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.33/10.41  tff('#skF_14', type, '#skF_14': $i).
% 20.33/10.41  tff('#skF_13', type, '#skF_13': $i).
% 20.33/10.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 20.33/10.41  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 20.33/10.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.33/10.41  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 20.33/10.41  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 20.33/10.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.33/10.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.33/10.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 20.33/10.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.33/10.41  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 20.33/10.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.33/10.41  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 20.33/10.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.33/10.41  tff('#skF_12', type, '#skF_12': $i).
% 20.33/10.41  
% 20.36/10.42  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(C, B)) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_relat_1)).
% 20.36/10.42  tff(f_68, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 20.36/10.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 20.36/10.42  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 20.36/10.42  tff(f_64, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 20.36/10.42  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 20.36/10.42  tff(c_54, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.36/10.42  tff(c_44, plain, (![A_61, B_62]: (v1_relat_1(k7_relat_1(A_61, B_62)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_68])).
% 20.36/10.42  tff(c_48, plain, (r1_tarski('#skF_14', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.36/10.42  tff(c_52, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.36/10.42  tff(c_57, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68, B_69), A_68) | r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.36/10.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.36/10.42  tff(c_62, plain, (![A_68]: (r1_tarski(A_68, A_68))), inference(resolution, [status(thm)], [c_57, c_4])).
% 20.36/10.42  tff(c_50, plain, (r1_tarski(k1_relat_1('#skF_14'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.36/10.42  tff(c_90, plain, (![A_84, B_85]: (r2_hidden(k4_tarski('#skF_6'(A_84, B_85), '#skF_7'(A_84, B_85)), A_84) | r1_tarski(A_84, B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_56])).
% 20.36/10.42  tff(c_34, plain, (![C_57, A_42, D_60]: (r2_hidden(C_57, k1_relat_1(A_42)) | ~r2_hidden(k4_tarski(C_57, D_60), A_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 20.36/10.42  tff(c_105, plain, (![A_88, B_89]: (r2_hidden('#skF_6'(A_88, B_89), k1_relat_1(A_88)) | r1_tarski(A_88, B_89) | ~v1_relat_1(A_88))), inference(resolution, [status(thm)], [c_90, c_34])).
% 20.36/10.42  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.36/10.42  tff(c_151, plain, (![A_100, B_101, B_102]: (r2_hidden('#skF_6'(A_100, B_101), B_102) | ~r1_tarski(k1_relat_1(A_100), B_102) | r1_tarski(A_100, B_101) | ~v1_relat_1(A_100))), inference(resolution, [status(thm)], [c_105, c_2])).
% 20.36/10.42  tff(c_2154, plain, (![A_243, B_244, B_245, B_246]: (r2_hidden('#skF_6'(A_243, B_244), B_245) | ~r1_tarski(B_246, B_245) | ~r1_tarski(k1_relat_1(A_243), B_246) | r1_tarski(A_243, B_244) | ~v1_relat_1(A_243))), inference(resolution, [status(thm)], [c_151, c_2])).
% 20.36/10.42  tff(c_2186, plain, (![A_249, B_250]: (r2_hidden('#skF_6'(A_249, B_250), '#skF_12') | ~r1_tarski(k1_relat_1(A_249), k1_relat_1('#skF_14')) | r1_tarski(A_249, B_250) | ~v1_relat_1(A_249))), inference(resolution, [status(thm)], [c_50, c_2154])).
% 20.36/10.42  tff(c_2195, plain, (![B_250]: (r2_hidden('#skF_6'('#skF_14', B_250), '#skF_12') | r1_tarski('#skF_14', B_250) | ~v1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_62, c_2186])).
% 20.36/10.42  tff(c_2202, plain, (![B_250]: (r2_hidden('#skF_6'('#skF_14', B_250), '#skF_12') | r1_tarski('#skF_14', B_250))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2195])).
% 20.36/10.42  tff(c_97, plain, (![A_84, B_85, B_2]: (r2_hidden(k4_tarski('#skF_6'(A_84, B_85), '#skF_7'(A_84, B_85)), B_2) | ~r1_tarski(A_84, B_2) | r1_tarski(A_84, B_85) | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_90, c_2])).
% 20.36/10.42  tff(c_881, plain, (![D_165, E_166, A_167, B_168]: (r2_hidden(k4_tarski(D_165, E_166), k7_relat_1(A_167, B_168)) | ~r2_hidden(k4_tarski(D_165, E_166), A_167) | ~r2_hidden(D_165, B_168) | ~v1_relat_1(k7_relat_1(A_167, B_168)) | ~v1_relat_1(A_167))), inference(cnfTransformation, [status(thm)], [f_46])).
% 20.36/10.42  tff(c_28, plain, (![A_25, B_35]: (~r2_hidden(k4_tarski('#skF_6'(A_25, B_35), '#skF_7'(A_25, B_35)), B_35) | r1_tarski(A_25, B_35) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 20.36/10.42  tff(c_13686, plain, (![A_552, A_553, B_554]: (r1_tarski(A_552, k7_relat_1(A_553, B_554)) | ~v1_relat_1(A_552) | ~r2_hidden(k4_tarski('#skF_6'(A_552, k7_relat_1(A_553, B_554)), '#skF_7'(A_552, k7_relat_1(A_553, B_554))), A_553) | ~r2_hidden('#skF_6'(A_552, k7_relat_1(A_553, B_554)), B_554) | ~v1_relat_1(k7_relat_1(A_553, B_554)) | ~v1_relat_1(A_553))), inference(resolution, [status(thm)], [c_881, c_28])).
% 20.36/10.42  tff(c_43936, plain, (![A_948, B_949, B_950]: (~r2_hidden('#skF_6'(A_948, k7_relat_1(B_949, B_950)), B_950) | ~v1_relat_1(k7_relat_1(B_949, B_950)) | ~v1_relat_1(B_949) | ~r1_tarski(A_948, B_949) | r1_tarski(A_948, k7_relat_1(B_949, B_950)) | ~v1_relat_1(A_948))), inference(resolution, [status(thm)], [c_97, c_13686])).
% 20.36/10.42  tff(c_44057, plain, (![B_949]: (~v1_relat_1(k7_relat_1(B_949, '#skF_12')) | ~v1_relat_1(B_949) | ~r1_tarski('#skF_14', B_949) | ~v1_relat_1('#skF_14') | r1_tarski('#skF_14', k7_relat_1(B_949, '#skF_12')))), inference(resolution, [status(thm)], [c_2202, c_43936])).
% 20.36/10.42  tff(c_44170, plain, (![B_951]: (~v1_relat_1(k7_relat_1(B_951, '#skF_12')) | ~v1_relat_1(B_951) | ~r1_tarski('#skF_14', B_951) | r1_tarski('#skF_14', k7_relat_1(B_951, '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44057])).
% 20.36/10.42  tff(c_46, plain, (~r1_tarski('#skF_14', k7_relat_1('#skF_13', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 20.36/10.42  tff(c_44224, plain, (~v1_relat_1(k7_relat_1('#skF_13', '#skF_12')) | ~v1_relat_1('#skF_13') | ~r1_tarski('#skF_14', '#skF_13')), inference(resolution, [status(thm)], [c_44170, c_46])).
% 20.36/10.42  tff(c_44259, plain, (~v1_relat_1(k7_relat_1('#skF_13', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_54, c_44224])).
% 20.36/10.42  tff(c_44264, plain, (~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_44, c_44259])).
% 20.36/10.42  tff(c_44268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_44264])).
% 20.36/10.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.36/10.42  
% 20.36/10.42  Inference rules
% 20.36/10.42  ----------------------
% 20.36/10.42  #Ref     : 0
% 20.36/10.42  #Sup     : 10356
% 20.36/10.42  #Fact    : 0
% 20.36/10.42  #Define  : 0
% 20.36/10.42  #Split   : 62
% 20.36/10.42  #Chain   : 0
% 20.36/10.42  #Close   : 0
% 20.36/10.42  
% 20.36/10.42  Ordering : KBO
% 20.36/10.42  
% 20.36/10.42  Simplification rules
% 20.36/10.42  ----------------------
% 20.36/10.42  #Subsume      : 3755
% 20.36/10.42  #Demod        : 2146
% 20.36/10.42  #Tautology    : 291
% 20.36/10.42  #SimpNegUnit  : 36
% 20.36/10.42  #BackRed      : 210
% 20.36/10.42  
% 20.36/10.42  #Partial instantiations: 0
% 20.36/10.42  #Strategies tried      : 1
% 20.36/10.42  
% 20.36/10.42  Timing (in seconds)
% 20.36/10.42  ----------------------
% 20.36/10.42  Preprocessing        : 0.31
% 20.36/10.42  Parsing              : 0.16
% 20.36/10.42  CNF conversion       : 0.03
% 20.36/10.42  Main loop            : 9.36
% 20.36/10.42  Inferencing          : 1.52
% 20.36/10.42  Reduction            : 1.75
% 20.36/10.42  Demodulation         : 1.00
% 20.36/10.42  BG Simplification    : 0.17
% 20.36/10.42  Subsumption          : 5.36
% 20.36/10.42  Abstraction          : 0.27
% 20.36/10.42  MUC search           : 0.00
% 20.36/10.42  Cooper               : 0.00
% 20.36/10.42  Total                : 9.69
% 20.36/10.42  Index Insertion      : 0.00
% 20.36/10.42  Index Deletion       : 0.00
% 20.36/10.42  Index Matching       : 0.00
% 20.36/10.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
