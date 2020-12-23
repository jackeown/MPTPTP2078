%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:44 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 126 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 224 expanded)
%              Number of equality atoms :   16 (  44 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_70,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_68,axiom,(
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

tff(f_78,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( v1_relat_1(D)
                 => ( ( r1_tarski(A,B)
                      & r1_tarski(C,D) )
                   => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_70,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_56,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_196,plain,(
    ! [A_117,B_118,C_119,D_120] : k3_enumset1(A_117,A_117,B_118,C_119,D_120) = k2_enumset1(A_117,B_118,C_119,D_120) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_22,B_23,G_30,D_25,C_24] : r2_hidden(G_30,k3_enumset1(A_22,B_23,C_24,D_25,G_30)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_286,plain,(
    ! [D_144,A_145,B_146,C_147] : r2_hidden(D_144,k2_enumset1(A_145,B_146,C_147,D_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_22])).

tff(c_293,plain,(
    ! [C_148,A_149,B_150] : r2_hidden(C_148,k1_enumset1(A_149,B_150,C_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_286])).

tff(c_309,plain,(
    ! [B_156,A_157] : r2_hidden(B_156,k2_tarski(A_157,B_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_293])).

tff(c_62,plain,(
    ! [B_36,A_35] :
      ( r1_tarski(k1_setfam_1(B_36),A_35)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_60,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,k1_zfmisc_1(B_34))
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_124,plain,(
    ! [B_99,A_100] :
      ( v1_relat_1(B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_100))
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_129,plain,(
    ! [A_101,B_102] :
      ( v1_relat_1(A_101)
      | ~ v1_relat_1(B_102)
      | ~ r1_tarski(A_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_60,c_124])).

tff(c_139,plain,(
    ! [B_36,A_35] :
      ( v1_relat_1(k1_setfam_1(B_36))
      | ~ v1_relat_1(A_35)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_62,c_129])).

tff(c_314,plain,(
    ! [A_157,B_156] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_157,B_156)))
      | ~ v1_relat_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_309,c_139])).

tff(c_317,plain,(
    ! [A_157,B_156] :
      ( v1_relat_1(k3_xboole_0(A_157,B_156))
      | ~ v1_relat_1(B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_314])).

tff(c_74,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [A_66,B_67] : k1_setfam_1(k2_tarski(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_86,plain,(
    ! [A_66,B_67,A_35] :
      ( r1_tarski(k3_xboole_0(A_66,B_67),A_35)
      | ~ r2_hidden(A_35,k2_tarski(A_66,B_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_62])).

tff(c_315,plain,(
    ! [A_157,B_156] : r1_tarski(k3_xboole_0(A_157,B_156),B_156) ),
    inference(resolution,[status(thm)],[c_309,c_86])).

tff(c_905,plain,(
    ! [A_238,C_239,B_240,D_241] :
      ( r1_tarski(k5_relat_1(A_238,C_239),k5_relat_1(B_240,D_241))
      | ~ r1_tarski(C_239,D_241)
      | ~ r1_tarski(A_238,B_240)
      | ~ v1_relat_1(D_241)
      | ~ v1_relat_1(C_239)
      | ~ v1_relat_1(B_240)
      | ~ v1_relat_1(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_72,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_598,plain,(
    ! [A_198,C_199,B_200,D_201] :
      ( r1_tarski(k5_relat_1(A_198,C_199),k5_relat_1(B_200,D_201))
      | ~ r1_tarski(C_199,D_201)
      | ~ r1_tarski(A_198,B_200)
      | ~ v1_relat_1(D_201)
      | ~ v1_relat_1(C_199)
      | ~ v1_relat_1(B_200)
      | ~ v1_relat_1(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_244,plain,(
    ! [A_130,B_131,C_132] :
      ( r1_tarski(A_130,k3_xboole_0(B_131,C_132))
      | ~ r1_tarski(A_130,C_132)
      | ~ r1_tarski(A_130,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_262,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_244,c_68])).

tff(c_332,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_601,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_598,c_332])).

tff(c_612,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6,c_8,c_601])).

tff(c_618,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_317,c_612])).

tff(c_625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_618])).

tff(c_626,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_908,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_905,c_626])).

tff(c_919,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_6,c_315,c_908])).

tff(c_925,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_317,c_919])).

tff(c_932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_925])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:20:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.50  
% 3.16/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.16/1.50  
% 3.16/1.50  %Foreground sorts:
% 3.16/1.50  
% 3.16/1.50  
% 3.16/1.50  %Background operators:
% 3.16/1.50  
% 3.16/1.50  
% 3.16/1.50  %Foreground operators:
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.16/1.50  
% 3.16/1.52  tff(f_113, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 3.16/1.52  tff(f_70, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.16/1.52  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.16/1.52  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.16/1.52  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.16/1.52  tff(f_68, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 3.16/1.52  tff(f_78, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.16/1.52  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.52  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.16/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.52  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 3.16/1.52  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.16/1.52  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.16/1.52  tff(c_70, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.16/1.52  tff(c_56, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.16/1.52  tff(c_12, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/1.52  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.52  tff(c_196, plain, (![A_117, B_118, C_119, D_120]: (k3_enumset1(A_117, A_117, B_118, C_119, D_120)=k2_enumset1(A_117, B_118, C_119, D_120))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/1.52  tff(c_22, plain, (![A_22, B_23, G_30, D_25, C_24]: (r2_hidden(G_30, k3_enumset1(A_22, B_23, C_24, D_25, G_30)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.16/1.52  tff(c_286, plain, (![D_144, A_145, B_146, C_147]: (r2_hidden(D_144, k2_enumset1(A_145, B_146, C_147, D_144)))), inference(superposition, [status(thm), theory('equality')], [c_196, c_22])).
% 3.16/1.52  tff(c_293, plain, (![C_148, A_149, B_150]: (r2_hidden(C_148, k1_enumset1(A_149, B_150, C_148)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_286])).
% 3.16/1.52  tff(c_309, plain, (![B_156, A_157]: (r2_hidden(B_156, k2_tarski(A_157, B_156)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_293])).
% 3.16/1.52  tff(c_62, plain, (![B_36, A_35]: (r1_tarski(k1_setfam_1(B_36), A_35) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.16/1.52  tff(c_60, plain, (![A_33, B_34]: (m1_subset_1(A_33, k1_zfmisc_1(B_34)) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.16/1.52  tff(c_124, plain, (![B_99, A_100]: (v1_relat_1(B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(A_100)) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.52  tff(c_129, plain, (![A_101, B_102]: (v1_relat_1(A_101) | ~v1_relat_1(B_102) | ~r1_tarski(A_101, B_102))), inference(resolution, [status(thm)], [c_60, c_124])).
% 3.16/1.52  tff(c_139, plain, (![B_36, A_35]: (v1_relat_1(k1_setfam_1(B_36)) | ~v1_relat_1(A_35) | ~r2_hidden(A_35, B_36))), inference(resolution, [status(thm)], [c_62, c_129])).
% 3.16/1.52  tff(c_314, plain, (![A_157, B_156]: (v1_relat_1(k1_setfam_1(k2_tarski(A_157, B_156))) | ~v1_relat_1(B_156))), inference(resolution, [status(thm)], [c_309, c_139])).
% 3.16/1.52  tff(c_317, plain, (![A_157, B_156]: (v1_relat_1(k3_xboole_0(A_157, B_156)) | ~v1_relat_1(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_314])).
% 3.16/1.52  tff(c_74, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.16/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.52  tff(c_80, plain, (![A_66, B_67]: (k1_setfam_1(k2_tarski(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.16/1.52  tff(c_86, plain, (![A_66, B_67, A_35]: (r1_tarski(k3_xboole_0(A_66, B_67), A_35) | ~r2_hidden(A_35, k2_tarski(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_62])).
% 3.16/1.52  tff(c_315, plain, (![A_157, B_156]: (r1_tarski(k3_xboole_0(A_157, B_156), B_156))), inference(resolution, [status(thm)], [c_309, c_86])).
% 3.16/1.52  tff(c_905, plain, (![A_238, C_239, B_240, D_241]: (r1_tarski(k5_relat_1(A_238, C_239), k5_relat_1(B_240, D_241)) | ~r1_tarski(C_239, D_241) | ~r1_tarski(A_238, B_240) | ~v1_relat_1(D_241) | ~v1_relat_1(C_239) | ~v1_relat_1(B_240) | ~v1_relat_1(A_238))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.16/1.52  tff(c_72, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.16/1.52  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.52  tff(c_598, plain, (![A_198, C_199, B_200, D_201]: (r1_tarski(k5_relat_1(A_198, C_199), k5_relat_1(B_200, D_201)) | ~r1_tarski(C_199, D_201) | ~r1_tarski(A_198, B_200) | ~v1_relat_1(D_201) | ~v1_relat_1(C_199) | ~v1_relat_1(B_200) | ~v1_relat_1(A_198))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.16/1.52  tff(c_244, plain, (![A_130, B_131, C_132]: (r1_tarski(A_130, k3_xboole_0(B_131, C_132)) | ~r1_tarski(A_130, C_132) | ~r1_tarski(A_130, B_131))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.52  tff(c_68, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.16/1.52  tff(c_262, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_244, c_68])).
% 3.16/1.52  tff(c_332, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_262])).
% 3.16/1.52  tff(c_601, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_598, c_332])).
% 3.16/1.52  tff(c_612, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_6, c_8, c_601])).
% 3.16/1.52  tff(c_618, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_317, c_612])).
% 3.16/1.52  tff(c_625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_618])).
% 3.16/1.52  tff(c_626, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_262])).
% 3.16/1.52  tff(c_908, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_905, c_626])).
% 3.16/1.52  tff(c_919, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_6, c_315, c_908])).
% 3.16/1.52  tff(c_925, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_317, c_919])).
% 3.16/1.52  tff(c_932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_925])).
% 3.16/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.52  
% 3.16/1.52  Inference rules
% 3.16/1.52  ----------------------
% 3.16/1.52  #Ref     : 0
% 3.16/1.52  #Sup     : 202
% 3.16/1.52  #Fact    : 0
% 3.16/1.52  #Define  : 0
% 3.16/1.52  #Split   : 2
% 3.16/1.52  #Chain   : 0
% 3.16/1.52  #Close   : 0
% 3.16/1.52  
% 3.16/1.52  Ordering : KBO
% 3.16/1.52  
% 3.16/1.52  Simplification rules
% 3.16/1.52  ----------------------
% 3.16/1.52  #Subsume      : 27
% 3.16/1.52  #Demod        : 99
% 3.16/1.52  #Tautology    : 110
% 3.16/1.52  #SimpNegUnit  : 0
% 3.16/1.52  #BackRed      : 0
% 3.16/1.52  
% 3.16/1.52  #Partial instantiations: 0
% 3.16/1.52  #Strategies tried      : 1
% 3.16/1.52  
% 3.16/1.52  Timing (in seconds)
% 3.16/1.52  ----------------------
% 3.16/1.52  Preprocessing        : 0.33
% 3.16/1.52  Parsing              : 0.16
% 3.16/1.52  CNF conversion       : 0.03
% 3.16/1.52  Main loop            : 0.37
% 3.16/1.52  Inferencing          : 0.13
% 3.16/1.52  Reduction            : 0.11
% 3.16/1.52  Demodulation         : 0.08
% 3.16/1.52  BG Simplification    : 0.02
% 3.16/1.52  Subsumption          : 0.09
% 3.16/1.52  Abstraction          : 0.03
% 3.16/1.52  MUC search           : 0.00
% 3.16/1.52  Cooper               : 0.00
% 3.16/1.52  Total                : 0.74
% 3.16/1.52  Index Insertion      : 0.00
% 3.16/1.52  Index Deletion       : 0.00
% 3.16/1.52  Index Matching       : 0.00
% 3.16/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
