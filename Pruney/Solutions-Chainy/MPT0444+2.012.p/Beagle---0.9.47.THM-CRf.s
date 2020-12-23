%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:22 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 134 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 221 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_145,plain,(
    ! [A_96,B_97,C_98,D_99] : k3_enumset1(A_96,A_96,B_97,C_98,D_99) = k2_enumset1(A_96,B_97,C_98,D_99) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [B_27,D_29,G_34,A_26,C_28] : r2_hidden(G_34,k3_enumset1(A_26,B_27,C_28,D_29,G_34)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_169,plain,(
    ! [D_100,A_101,B_102,C_103] : r2_hidden(D_100,k2_enumset1(A_101,B_102,C_103,D_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_18])).

tff(c_176,plain,(
    ! [C_104,A_105,B_106] : r2_hidden(C_104,k1_enumset1(A_105,B_106,C_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_169])).

tff(c_181,plain,(
    ! [B_7,A_6] : r2_hidden(B_7,k2_tarski(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_176])).

tff(c_88,plain,(
    ! [A_58,B_59] : k1_setfam_1(k2_tarski(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,(
    ! [B_40,A_39] :
      ( r1_tarski(k1_setfam_1(B_40),A_39)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_389,plain,(
    ! [A_198,B_199,A_200] :
      ( r1_tarski(k3_xboole_0(A_198,B_199),A_200)
      | ~ r2_hidden(A_200,k2_tarski(A_198,B_199)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_58])).

tff(c_398,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),B_7) ),
    inference(resolution,[status(thm)],[c_181,c_389])).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_183,plain,(
    ! [B_107,A_108] : r2_hidden(B_107,k2_tarski(A_108,B_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_176])).

tff(c_56,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_103,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_108,plain,(
    ! [A_77,B_78] :
      ( v1_relat_1(A_77)
      | ~ v1_relat_1(B_78)
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_115,plain,(
    ! [B_40,A_39] :
      ( v1_relat_1(k1_setfam_1(B_40))
      | ~ v1_relat_1(A_39)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_58,c_108])).

tff(c_185,plain,(
    ! [A_108,B_107] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_108,B_107)))
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_183,c_115])).

tff(c_187,plain,(
    ! [A_108,B_107] :
      ( v1_relat_1(k3_xboole_0(A_108,B_107))
      | ~ v1_relat_1(B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_185])).

tff(c_316,plain,(
    ! [A_160,B_161] :
      ( r1_tarski(k2_relat_1(A_160),k2_relat_1(B_161))
      | ~ r1_tarski(A_160,B_161)
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_70,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_266,plain,(
    ! [A_149,B_150] :
      ( r1_tarski(k2_relat_1(A_149),k2_relat_1(B_150))
      | ~ r1_tarski(A_149,B_150)
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_196,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_tarski(A_115,k3_xboole_0(B_116,C_117))
      | ~ r1_tarski(A_115,C_117)
      | ~ r1_tarski(A_115,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_204,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_196,c_66])).

tff(c_224,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_269,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_266,c_224])).

tff(c_275,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2,c_269])).

tff(c_279,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_187,c_275])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_279])).

tff(c_287,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_319,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_316,c_287])).

tff(c_325,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_319])).

tff(c_342,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_345,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_187,c_342])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_345])).

tff(c_353,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:55:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.87  
% 3.27/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.87  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 3.27/1.87  
% 3.27/1.87  %Foreground sorts:
% 3.27/1.87  
% 3.27/1.87  
% 3.27/1.87  %Background operators:
% 3.27/1.87  
% 3.27/1.87  
% 3.27/1.87  %Foreground operators:
% 3.27/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.27/1.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.27/1.87  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.87  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.87  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.27/1.87  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.27/1.87  
% 3.27/1.89  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.27/1.89  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.27/1.89  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.27/1.89  tff(f_64, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 3.27/1.89  tff(f_66, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.27/1.89  tff(f_74, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.27/1.89  tff(f_100, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 3.27/1.89  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.27/1.89  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.27/1.89  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.27/1.89  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.27/1.89  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.27/1.89  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.89  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.89  tff(c_145, plain, (![A_96, B_97, C_98, D_99]: (k3_enumset1(A_96, A_96, B_97, C_98, D_99)=k2_enumset1(A_96, B_97, C_98, D_99))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.27/1.89  tff(c_18, plain, (![B_27, D_29, G_34, A_26, C_28]: (r2_hidden(G_34, k3_enumset1(A_26, B_27, C_28, D_29, G_34)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.27/1.89  tff(c_169, plain, (![D_100, A_101, B_102, C_103]: (r2_hidden(D_100, k2_enumset1(A_101, B_102, C_103, D_100)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_18])).
% 3.27/1.89  tff(c_176, plain, (![C_104, A_105, B_106]: (r2_hidden(C_104, k1_enumset1(A_105, B_106, C_104)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_169])).
% 3.27/1.89  tff(c_181, plain, (![B_7, A_6]: (r2_hidden(B_7, k2_tarski(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_176])).
% 3.27/1.89  tff(c_88, plain, (![A_58, B_59]: (k1_setfam_1(k2_tarski(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.27/1.89  tff(c_58, plain, (![B_40, A_39]: (r1_tarski(k1_setfam_1(B_40), A_39) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.27/1.89  tff(c_389, plain, (![A_198, B_199, A_200]: (r1_tarski(k3_xboole_0(A_198, B_199), A_200) | ~r2_hidden(A_200, k2_tarski(A_198, B_199)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_58])).
% 3.27/1.89  tff(c_398, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), B_7))), inference(resolution, [status(thm)], [c_181, c_389])).
% 3.27/1.89  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.27/1.89  tff(c_52, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.27/1.89  tff(c_183, plain, (![B_107, A_108]: (r2_hidden(B_107, k2_tarski(A_108, B_107)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_176])).
% 3.27/1.89  tff(c_56, plain, (![A_37, B_38]: (m1_subset_1(A_37, k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.27/1.89  tff(c_103, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.27/1.89  tff(c_108, plain, (![A_77, B_78]: (v1_relat_1(A_77) | ~v1_relat_1(B_78) | ~r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_56, c_103])).
% 3.27/1.89  tff(c_115, plain, (![B_40, A_39]: (v1_relat_1(k1_setfam_1(B_40)) | ~v1_relat_1(A_39) | ~r2_hidden(A_39, B_40))), inference(resolution, [status(thm)], [c_58, c_108])).
% 3.27/1.89  tff(c_185, plain, (![A_108, B_107]: (v1_relat_1(k1_setfam_1(k2_tarski(A_108, B_107))) | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_183, c_115])).
% 3.27/1.89  tff(c_187, plain, (![A_108, B_107]: (v1_relat_1(k3_xboole_0(A_108, B_107)) | ~v1_relat_1(B_107))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_185])).
% 3.27/1.89  tff(c_316, plain, (![A_160, B_161]: (r1_tarski(k2_relat_1(A_160), k2_relat_1(B_161)) | ~r1_tarski(A_160, B_161) | ~v1_relat_1(B_161) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.27/1.89  tff(c_70, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.27/1.89  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.89  tff(c_266, plain, (![A_149, B_150]: (r1_tarski(k2_relat_1(A_149), k2_relat_1(B_150)) | ~r1_tarski(A_149, B_150) | ~v1_relat_1(B_150) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.27/1.89  tff(c_196, plain, (![A_115, B_116, C_117]: (r1_tarski(A_115, k3_xboole_0(B_116, C_117)) | ~r1_tarski(A_115, C_117) | ~r1_tarski(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.89  tff(c_66, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.27/1.89  tff(c_204, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_196, c_66])).
% 3.27/1.89  tff(c_224, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_204])).
% 3.27/1.89  tff(c_269, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_266, c_224])).
% 3.27/1.89  tff(c_275, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2, c_269])).
% 3.27/1.89  tff(c_279, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_187, c_275])).
% 3.27/1.89  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_279])).
% 3.27/1.89  tff(c_287, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_204])).
% 3.27/1.89  tff(c_319, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_316, c_287])).
% 3.27/1.89  tff(c_325, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_319])).
% 3.27/1.89  tff(c_342, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_325])).
% 3.27/1.89  tff(c_345, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_187, c_342])).
% 3.27/1.89  tff(c_352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_345])).
% 3.27/1.89  tff(c_353, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_325])).
% 3.27/1.89  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_398, c_353])).
% 3.27/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.89  
% 3.27/1.89  Inference rules
% 3.27/1.89  ----------------------
% 3.27/1.89  #Ref     : 0
% 3.27/1.89  #Sup     : 73
% 3.27/1.89  #Fact    : 0
% 3.27/1.90  #Define  : 0
% 3.27/1.90  #Split   : 3
% 3.27/1.90  #Chain   : 0
% 3.27/1.90  #Close   : 0
% 3.27/1.90  
% 3.27/1.90  Ordering : KBO
% 3.27/1.90  
% 3.27/1.90  Simplification rules
% 3.27/1.90  ----------------------
% 3.27/1.90  #Subsume      : 12
% 3.27/1.90  #Demod        : 21
% 3.27/1.90  #Tautology    : 20
% 3.27/1.90  #SimpNegUnit  : 0
% 3.27/1.90  #BackRed      : 1
% 3.27/1.90  
% 3.27/1.90  #Partial instantiations: 0
% 3.27/1.90  #Strategies tried      : 1
% 3.27/1.90  
% 3.27/1.90  Timing (in seconds)
% 3.27/1.90  ----------------------
% 3.27/1.90  Preprocessing        : 0.58
% 3.27/1.90  Parsing              : 0.29
% 3.27/1.90  CNF conversion       : 0.04
% 3.27/1.90  Main loop            : 0.44
% 3.27/1.90  Inferencing          : 0.16
% 3.27/1.90  Reduction            : 0.13
% 3.27/1.90  Demodulation         : 0.09
% 3.27/1.90  BG Simplification    : 0.03
% 3.27/1.90  Subsumption          : 0.10
% 3.27/1.90  Abstraction          : 0.03
% 3.27/1.90  MUC search           : 0.00
% 3.27/1.90  Cooper               : 0.00
% 3.27/1.90  Total                : 1.08
% 3.27/1.90  Index Insertion      : 0.00
% 3.27/1.90  Index Deletion       : 0.00
% 3.27/1.90  Index Matching       : 0.00
% 3.27/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
