%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:06 EST 2020

% Result     : Theorem 6.82s
% Output     : CNFRefutation 6.82s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 174 expanded)
%              Number of leaves         :   26 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  154 ( 442 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

tff(f_94,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_70,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ! [C] :
              ( v3_ordinal1(C)
             => ( ( r1_tarski(A,B)
                  & r2_hidden(B,C) )
               => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

tff(c_38,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    ! [A_30] :
      ( v3_ordinal1(k1_ordinal1(A_30))
      | ~ v3_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_3'(A_14),A_14)
      | v1_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    ! [A_41,B_42] :
      ( v3_ordinal1(A_41)
      | ~ r2_hidden(A_41,B_42)
      | ~ v3_ordinal1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_61,plain,(
    ! [A_14] :
      ( v3_ordinal1('#skF_3'(A_14))
      | ~ v3_ordinal1(A_14)
      | v1_ordinal1(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_54])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( r1_ordinal1(B_13,A_12)
      | r1_ordinal1(A_12,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_299,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(A_88,B_89)
      | ~ r1_ordinal1(A_88,B_89)
      | ~ v3_ordinal1(B_89)
      | ~ v3_ordinal1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_14] :
      ( ~ r1_tarski('#skF_3'(A_14),A_14)
      | v1_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_818,plain,(
    ! [B_124] :
      ( v1_ordinal1(B_124)
      | ~ r1_ordinal1('#skF_3'(B_124),B_124)
      | ~ v3_ordinal1(B_124)
      | ~ v3_ordinal1('#skF_3'(B_124)) ) ),
    inference(resolution,[status(thm)],[c_299,c_18])).

tff(c_828,plain,(
    ! [B_13] :
      ( v1_ordinal1(B_13)
      | r1_ordinal1(B_13,'#skF_3'(B_13))
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1('#skF_3'(B_13)) ) ),
    inference(resolution,[status(thm)],[c_14,c_818])).

tff(c_43,plain,(
    ! [B_37,A_38] :
      ( ~ r1_tarski(B_37,A_38)
      | ~ r2_hidden(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    ! [A_14] :
      ( ~ r1_tarski(A_14,'#skF_3'(A_14))
      | v1_ordinal1(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_1228,plain,(
    ! [A_156] :
      ( v1_ordinal1(A_156)
      | ~ r1_ordinal1(A_156,'#skF_3'(A_156))
      | ~ v3_ordinal1('#skF_3'(A_156))
      | ~ v3_ordinal1(A_156) ) ),
    inference(resolution,[status(thm)],[c_299,c_50])).

tff(c_1237,plain,(
    ! [B_157] :
      ( v1_ordinal1(B_157)
      | ~ v3_ordinal1(B_157)
      | ~ v3_ordinal1('#skF_3'(B_157)) ) ),
    inference(resolution,[status(thm)],[c_828,c_1228])).

tff(c_1242,plain,(
    ! [A_158] :
      ( ~ v3_ordinal1(A_158)
      | v1_ordinal1(A_158) ) ),
    inference(resolution,[status(thm)],[c_61,c_1237])).

tff(c_1266,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_1242])).

tff(c_100,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),A_55)
      | r1_tarski(k3_tarski(A_55),B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [B_17,A_14] :
      ( r1_tarski(B_17,A_14)
      | ~ r2_hidden(B_17,A_14)
      | ~ v1_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_579,plain,(
    ! [A_111,B_112] :
      ( r1_tarski('#skF_2'(A_111,B_112),A_111)
      | ~ v1_ordinal1(A_111)
      | r1_tarski(k3_tarski(A_111),B_112) ) ),
    inference(resolution,[status(thm)],[c_100,c_16])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r1_tarski('#skF_2'(A_6,B_7),B_7)
      | r1_tarski(k3_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_613,plain,(
    ! [A_111] :
      ( ~ v1_ordinal1(A_111)
      | r1_tarski(k3_tarski(A_111),A_111) ) ),
    inference(resolution,[status(thm)],[c_579,c_8])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_1'(A_47,B_48),B_48)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_113,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,(
    ! [A_14,B_58] :
      ( r2_hidden('#skF_3'(A_14),B_58)
      | ~ r1_tarski(A_14,B_58)
      | v1_ordinal1(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_113])).

tff(c_157,plain,(
    ! [C_70,B_71,A_72] :
      ( r1_tarski(C_70,B_71)
      | ~ r2_hidden(C_70,A_72)
      | ~ r1_tarski(k3_tarski(A_72),B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3330,plain,(
    ! [A_271,B_272,B_273] :
      ( r1_tarski('#skF_3'(A_271),B_272)
      | ~ r1_tarski(k3_tarski(B_273),B_272)
      | ~ r1_tarski(A_271,B_273)
      | v1_ordinal1(A_271) ) ),
    inference(resolution,[status(thm)],[c_124,c_157])).

tff(c_3424,plain,(
    ! [A_274,B_275] :
      ( r1_tarski('#skF_3'(A_274),k3_tarski(B_275))
      | ~ r1_tarski(A_274,B_275)
      | v1_ordinal1(A_274) ) ),
    inference(resolution,[status(thm)],[c_83,c_3330])).

tff(c_3454,plain,(
    ! [B_276] :
      ( ~ r1_tarski(k3_tarski(B_276),B_276)
      | v1_ordinal1(k3_tarski(B_276)) ) ),
    inference(resolution,[status(thm)],[c_3424,c_18])).

tff(c_3470,plain,(
    ! [A_111] :
      ( v1_ordinal1(k3_tarski(A_111))
      | ~ v1_ordinal1(A_111) ) ),
    inference(resolution,[status(thm)],[c_613,c_3454])).

tff(c_26,plain,(
    ! [A_20] : r2_hidden(A_20,k1_ordinal1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_390,plain,(
    ! [A_95,C_96,B_97] :
      ( r2_hidden(A_95,C_96)
      | ~ r2_hidden(B_97,C_96)
      | ~ r1_tarski(A_95,B_97)
      | ~ v3_ordinal1(C_96)
      | ~ v3_ordinal1(B_97)
      | ~ v1_ordinal1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1380,plain,(
    ! [A_176,A_177] :
      ( r2_hidden(A_176,k1_ordinal1(A_177))
      | ~ r1_tarski(A_176,A_177)
      | ~ v3_ordinal1(k1_ordinal1(A_177))
      | ~ v3_ordinal1(A_177)
      | ~ v1_ordinal1(A_176) ) ),
    inference(resolution,[status(thm)],[c_26,c_390])).

tff(c_30,plain,(
    ! [A_28,B_29] :
      ( v3_ordinal1(A_28)
      | ~ r2_hidden(A_28,B_29)
      | ~ v3_ordinal1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1970,plain,(
    ! [A_204,A_205] :
      ( v3_ordinal1(A_204)
      | ~ r1_tarski(A_204,A_205)
      | ~ v3_ordinal1(k1_ordinal1(A_205))
      | ~ v3_ordinal1(A_205)
      | ~ v1_ordinal1(A_204) ) ),
    inference(resolution,[status(thm)],[c_1380,c_30])).

tff(c_6687,plain,(
    ! [A_370] :
      ( v3_ordinal1(k3_tarski(A_370))
      | ~ v3_ordinal1(k1_ordinal1(A_370))
      | ~ v3_ordinal1(A_370)
      | ~ v1_ordinal1(k3_tarski(A_370))
      | ~ v1_ordinal1(A_370) ) ),
    inference(resolution,[status(thm)],[c_613,c_1970])).

tff(c_36,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6738,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_4'))
    | ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1(k3_tarski('#skF_4'))
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6687,c_36])).

tff(c_6757,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_4'))
    | ~ v1_ordinal1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_38,c_6738])).

tff(c_6889,plain,(
    ~ v1_ordinal1(k3_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6757])).

tff(c_6895,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3470,c_6889])).

tff(c_6902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_6895])).

tff(c_6903,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6757])).

tff(c_6907,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_6903])).

tff(c_6911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6907])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:45:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.82/2.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.82/2.55  
% 6.82/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.82/2.55  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 6.82/2.55  
% 6.82/2.55  %Foreground sorts:
% 6.82/2.55  
% 6.82/2.55  
% 6.82/2.55  %Background operators:
% 6.82/2.55  
% 6.82/2.55  
% 6.82/2.55  %Foreground operators:
% 6.82/2.55  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.82/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.82/2.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.82/2.55  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 6.82/2.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.82/2.55  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.82/2.55  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.82/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.82/2.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.82/2.55  tff('#skF_4', type, '#skF_4': $i).
% 6.82/2.55  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.82/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.82/2.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.82/2.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.82/2.55  
% 6.82/2.56  tff(f_104, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_ordinal1)).
% 6.82/2.56  tff(f_94, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 6.82/2.56  tff(f_60, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 6.82/2.56  tff(f_90, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 6.82/2.56  tff(f_53, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 6.82/2.56  tff(f_68, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 6.82/2.56  tff(f_99, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.82/2.56  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 6.82/2.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.82/2.56  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 6.82/2.56  tff(f_70, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 6.82/2.56  tff(f_84, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_ordinal1)).
% 6.82/2.56  tff(c_38, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.82/2.56  tff(c_32, plain, (![A_30]: (v3_ordinal1(k1_ordinal1(A_30)) | ~v3_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.82/2.56  tff(c_20, plain, (![A_14]: (r2_hidden('#skF_3'(A_14), A_14) | v1_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.82/2.56  tff(c_54, plain, (![A_41, B_42]: (v3_ordinal1(A_41) | ~r2_hidden(A_41, B_42) | ~v3_ordinal1(B_42))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.82/2.56  tff(c_61, plain, (![A_14]: (v3_ordinal1('#skF_3'(A_14)) | ~v3_ordinal1(A_14) | v1_ordinal1(A_14))), inference(resolution, [status(thm)], [c_20, c_54])).
% 6.82/2.56  tff(c_14, plain, (![B_13, A_12]: (r1_ordinal1(B_13, A_12) | r1_ordinal1(A_12, B_13) | ~v3_ordinal1(B_13) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.82/2.56  tff(c_299, plain, (![A_88, B_89]: (r1_tarski(A_88, B_89) | ~r1_ordinal1(A_88, B_89) | ~v3_ordinal1(B_89) | ~v3_ordinal1(A_88))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.82/2.56  tff(c_18, plain, (![A_14]: (~r1_tarski('#skF_3'(A_14), A_14) | v1_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.82/2.56  tff(c_818, plain, (![B_124]: (v1_ordinal1(B_124) | ~r1_ordinal1('#skF_3'(B_124), B_124) | ~v3_ordinal1(B_124) | ~v3_ordinal1('#skF_3'(B_124)))), inference(resolution, [status(thm)], [c_299, c_18])).
% 6.82/2.56  tff(c_828, plain, (![B_13]: (v1_ordinal1(B_13) | r1_ordinal1(B_13, '#skF_3'(B_13)) | ~v3_ordinal1(B_13) | ~v3_ordinal1('#skF_3'(B_13)))), inference(resolution, [status(thm)], [c_14, c_818])).
% 6.82/2.56  tff(c_43, plain, (![B_37, A_38]: (~r1_tarski(B_37, A_38) | ~r2_hidden(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.82/2.56  tff(c_50, plain, (![A_14]: (~r1_tarski(A_14, '#skF_3'(A_14)) | v1_ordinal1(A_14))), inference(resolution, [status(thm)], [c_20, c_43])).
% 6.82/2.56  tff(c_1228, plain, (![A_156]: (v1_ordinal1(A_156) | ~r1_ordinal1(A_156, '#skF_3'(A_156)) | ~v3_ordinal1('#skF_3'(A_156)) | ~v3_ordinal1(A_156))), inference(resolution, [status(thm)], [c_299, c_50])).
% 6.82/2.56  tff(c_1237, plain, (![B_157]: (v1_ordinal1(B_157) | ~v3_ordinal1(B_157) | ~v3_ordinal1('#skF_3'(B_157)))), inference(resolution, [status(thm)], [c_828, c_1228])).
% 6.82/2.56  tff(c_1242, plain, (![A_158]: (~v3_ordinal1(A_158) | v1_ordinal1(A_158))), inference(resolution, [status(thm)], [c_61, c_1237])).
% 6.82/2.56  tff(c_1266, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_1242])).
% 6.82/2.56  tff(c_100, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), A_55) | r1_tarski(k3_tarski(A_55), B_56))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.82/2.56  tff(c_16, plain, (![B_17, A_14]: (r1_tarski(B_17, A_14) | ~r2_hidden(B_17, A_14) | ~v1_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.82/2.56  tff(c_579, plain, (![A_111, B_112]: (r1_tarski('#skF_2'(A_111, B_112), A_111) | ~v1_ordinal1(A_111) | r1_tarski(k3_tarski(A_111), B_112))), inference(resolution, [status(thm)], [c_100, c_16])).
% 6.82/2.56  tff(c_8, plain, (![A_6, B_7]: (~r1_tarski('#skF_2'(A_6, B_7), B_7) | r1_tarski(k3_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.82/2.56  tff(c_613, plain, (![A_111]: (~v1_ordinal1(A_111) | r1_tarski(k3_tarski(A_111), A_111))), inference(resolution, [status(thm)], [c_579, c_8])).
% 6.82/2.56  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.82/2.56  tff(c_78, plain, (![A_47, B_48]: (~r2_hidden('#skF_1'(A_47, B_48), B_48) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.82/2.56  tff(c_83, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_78])).
% 6.82/2.56  tff(c_113, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.82/2.56  tff(c_124, plain, (![A_14, B_58]: (r2_hidden('#skF_3'(A_14), B_58) | ~r1_tarski(A_14, B_58) | v1_ordinal1(A_14))), inference(resolution, [status(thm)], [c_20, c_113])).
% 6.82/2.56  tff(c_157, plain, (![C_70, B_71, A_72]: (r1_tarski(C_70, B_71) | ~r2_hidden(C_70, A_72) | ~r1_tarski(k3_tarski(A_72), B_71))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.82/2.56  tff(c_3330, plain, (![A_271, B_272, B_273]: (r1_tarski('#skF_3'(A_271), B_272) | ~r1_tarski(k3_tarski(B_273), B_272) | ~r1_tarski(A_271, B_273) | v1_ordinal1(A_271))), inference(resolution, [status(thm)], [c_124, c_157])).
% 6.82/2.56  tff(c_3424, plain, (![A_274, B_275]: (r1_tarski('#skF_3'(A_274), k3_tarski(B_275)) | ~r1_tarski(A_274, B_275) | v1_ordinal1(A_274))), inference(resolution, [status(thm)], [c_83, c_3330])).
% 6.82/2.56  tff(c_3454, plain, (![B_276]: (~r1_tarski(k3_tarski(B_276), B_276) | v1_ordinal1(k3_tarski(B_276)))), inference(resolution, [status(thm)], [c_3424, c_18])).
% 6.82/2.56  tff(c_3470, plain, (![A_111]: (v1_ordinal1(k3_tarski(A_111)) | ~v1_ordinal1(A_111))), inference(resolution, [status(thm)], [c_613, c_3454])).
% 6.82/2.56  tff(c_26, plain, (![A_20]: (r2_hidden(A_20, k1_ordinal1(A_20)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.82/2.56  tff(c_390, plain, (![A_95, C_96, B_97]: (r2_hidden(A_95, C_96) | ~r2_hidden(B_97, C_96) | ~r1_tarski(A_95, B_97) | ~v3_ordinal1(C_96) | ~v3_ordinal1(B_97) | ~v1_ordinal1(A_95))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.82/2.56  tff(c_1380, plain, (![A_176, A_177]: (r2_hidden(A_176, k1_ordinal1(A_177)) | ~r1_tarski(A_176, A_177) | ~v3_ordinal1(k1_ordinal1(A_177)) | ~v3_ordinal1(A_177) | ~v1_ordinal1(A_176))), inference(resolution, [status(thm)], [c_26, c_390])).
% 6.82/2.56  tff(c_30, plain, (![A_28, B_29]: (v3_ordinal1(A_28) | ~r2_hidden(A_28, B_29) | ~v3_ordinal1(B_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.82/2.56  tff(c_1970, plain, (![A_204, A_205]: (v3_ordinal1(A_204) | ~r1_tarski(A_204, A_205) | ~v3_ordinal1(k1_ordinal1(A_205)) | ~v3_ordinal1(A_205) | ~v1_ordinal1(A_204))), inference(resolution, [status(thm)], [c_1380, c_30])).
% 6.82/2.56  tff(c_6687, plain, (![A_370]: (v3_ordinal1(k3_tarski(A_370)) | ~v3_ordinal1(k1_ordinal1(A_370)) | ~v3_ordinal1(A_370) | ~v1_ordinal1(k3_tarski(A_370)) | ~v1_ordinal1(A_370))), inference(resolution, [status(thm)], [c_613, c_1970])).
% 6.82/2.56  tff(c_36, plain, (~v3_ordinal1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.82/2.56  tff(c_6738, plain, (~v3_ordinal1(k1_ordinal1('#skF_4')) | ~v3_ordinal1('#skF_4') | ~v1_ordinal1(k3_tarski('#skF_4')) | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_6687, c_36])).
% 6.82/2.56  tff(c_6757, plain, (~v3_ordinal1(k1_ordinal1('#skF_4')) | ~v1_ordinal1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_38, c_6738])).
% 6.82/2.56  tff(c_6889, plain, (~v1_ordinal1(k3_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_6757])).
% 6.82/2.56  tff(c_6895, plain, (~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_3470, c_6889])).
% 6.82/2.56  tff(c_6902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1266, c_6895])).
% 6.82/2.56  tff(c_6903, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_6757])).
% 6.82/2.56  tff(c_6907, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_6903])).
% 6.82/2.56  tff(c_6911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_6907])).
% 6.82/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.82/2.56  
% 6.82/2.56  Inference rules
% 6.82/2.56  ----------------------
% 6.82/2.56  #Ref     : 0
% 6.82/2.56  #Sup     : 1532
% 6.82/2.56  #Fact    : 2
% 6.82/2.56  #Define  : 0
% 6.82/2.56  #Split   : 1
% 6.82/2.56  #Chain   : 0
% 6.82/2.56  #Close   : 0
% 6.82/2.56  
% 6.82/2.56  Ordering : KBO
% 6.82/2.56  
% 6.82/2.56  Simplification rules
% 6.82/2.56  ----------------------
% 6.82/2.56  #Subsume      : 118
% 6.82/2.56  #Demod        : 31
% 6.82/2.56  #Tautology    : 33
% 6.82/2.56  #SimpNegUnit  : 0
% 6.82/2.56  #BackRed      : 0
% 6.82/2.56  
% 6.82/2.56  #Partial instantiations: 0
% 6.82/2.56  #Strategies tried      : 1
% 6.82/2.56  
% 6.82/2.56  Timing (in seconds)
% 6.82/2.56  ----------------------
% 6.82/2.57  Preprocessing        : 0.28
% 6.82/2.57  Parsing              : 0.16
% 6.82/2.57  CNF conversion       : 0.02
% 6.82/2.57  Main loop            : 1.52
% 6.82/2.57  Inferencing          : 0.46
% 6.82/2.57  Reduction            : 0.41
% 6.82/2.57  Demodulation         : 0.27
% 6.82/2.57  BG Simplification    : 0.05
% 6.82/2.57  Subsumption          : 0.47
% 6.82/2.57  Abstraction          : 0.07
% 6.82/2.57  MUC search           : 0.00
% 6.82/2.57  Cooper               : 0.00
% 6.82/2.57  Total                : 1.84
% 6.82/2.57  Index Insertion      : 0.00
% 6.82/2.57  Index Deletion       : 0.00
% 6.82/2.57  Index Matching       : 0.00
% 6.82/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
