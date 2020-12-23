%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:08 EST 2020

% Result     : Theorem 7.14s
% Output     : CNFRefutation 7.14s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 103 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  112 ( 181 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( r1_tarski(B,k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)))
                 => r1_tarski(B,k5_setfam_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)),k5_setfam_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).

tff(f_33,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_35,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [A_18,B_22,C_24] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_18,B_22)),k1_tops_2(A_18,B_22,C_24)),k5_setfam_1(u1_struct_0(A_18),C_24))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_4] : k3_tarski(k1_tarski(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(A_3,k1_zfmisc_1(k3_tarski(A_3))) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | ~ r1_tarski(k1_tarski(A_43),B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [A_43] : r2_hidden(A_43,k1_zfmisc_1(k3_tarski(k1_tarski(A_43)))) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_115,plain,(
    ! [A_43] : r2_hidden(A_43,k1_zfmisc_1(A_43)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_110])).

tff(c_12,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_120,plain,(
    ! [C_49,B_50,A_51] :
      ( ~ v1_xboole_0(C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_133,plain,(
    ! [A_52,A_53] :
      ( ~ v1_xboole_0(A_52)
      | ~ r2_hidden(A_53,A_52) ) ),
    inference(resolution,[status(thm)],[c_37,c_120])).

tff(c_145,plain,(
    ! [A_43] : ~ v1_xboole_0(k1_zfmisc_1(A_43)) ),
    inference(resolution,[status(thm)],[c_115,c_133])).

tff(c_10,plain,(
    ! [A_5] : k3_tarski(k1_zfmisc_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_92,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(resolution,[status(thm)],[c_37,c_76])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_146,plain,(
    ! [C_54,B_55,A_56] :
      ( r1_tarski(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(k3_tarski(A_56),B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_231,plain,(
    ! [A_72,B_73,B_74] :
      ( r1_tarski(A_72,B_73)
      | ~ r1_tarski(k3_tarski(B_74),B_73)
      | v1_xboole_0(B_74)
      | ~ m1_subset_1(A_72,B_74) ) ),
    inference(resolution,[status(thm)],[c_16,c_146])).

tff(c_246,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(A_75,k3_tarski(B_76))
      | v1_xboole_0(B_76)
      | ~ m1_subset_1(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_92,c_231])).

tff(c_153,plain,(
    ! [A_8,B_55,B_9] :
      ( r1_tarski(A_8,B_55)
      | ~ r1_tarski(k3_tarski(B_9),B_55)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_146])).

tff(c_2083,plain,(
    ! [A_222,B_223,B_224] :
      ( r1_tarski(A_222,k3_tarski(B_223))
      | v1_xboole_0(B_224)
      | ~ m1_subset_1(A_222,B_224)
      | v1_xboole_0(B_223)
      | ~ m1_subset_1(k3_tarski(B_224),B_223) ) ),
    inference(resolution,[status(thm)],[c_246,c_153])).

tff(c_2085,plain,(
    ! [A_10,B_223,B_11] :
      ( r1_tarski(A_10,k3_tarski(B_223))
      | v1_xboole_0(k1_zfmisc_1(B_11))
      | v1_xboole_0(B_223)
      | ~ m1_subset_1(k3_tarski(k1_zfmisc_1(B_11)),B_223)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_20,c_2083])).

tff(c_2093,plain,(
    ! [A_10,B_223,B_11] :
      ( r1_tarski(A_10,k3_tarski(B_223))
      | v1_xboole_0(k1_zfmisc_1(B_11))
      | v1_xboole_0(B_223)
      | ~ m1_subset_1(B_11,B_223)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2085])).

tff(c_2320,plain,(
    ! [A_243,B_244,B_245] :
      ( r1_tarski(A_243,k3_tarski(B_244))
      | v1_xboole_0(B_244)
      | ~ m1_subset_1(B_245,B_244)
      | ~ r1_tarski(A_243,B_245) ) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_2093])).

tff(c_2322,plain,(
    ! [A_243,B_11,A_10] :
      ( r1_tarski(A_243,k3_tarski(k1_zfmisc_1(B_11)))
      | v1_xboole_0(k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_243,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_20,c_2320])).

tff(c_2330,plain,(
    ! [A_243,B_11,A_10] :
      ( r1_tarski(A_243,B_11)
      | v1_xboole_0(k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_243,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2322])).

tff(c_2468,plain,(
    ! [A_250,B_251,A_252] :
      ( r1_tarski(A_250,B_251)
      | ~ r1_tarski(A_250,A_252)
      | ~ r1_tarski(A_252,B_251) ) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_2330])).

tff(c_3021,plain,(
    ! [B_266] :
      ( r1_tarski('#skF_2',B_266)
      | ~ r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3')),B_266) ) ),
    inference(resolution,[status(thm)],[c_30,c_2468])).

tff(c_3109,plain,
    ( r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_3021])).

tff(c_3150,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_3109])).

tff(c_3152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_3150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.14/2.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.14/2.71  
% 7.14/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.14/2.72  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 7.14/2.72  
% 7.14/2.72  %Foreground sorts:
% 7.14/2.72  
% 7.14/2.72  
% 7.14/2.72  %Background operators:
% 7.14/2.72  
% 7.14/2.72  
% 7.14/2.72  %Foreground operators:
% 7.14/2.72  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 7.14/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.14/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.14/2.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.14/2.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.14/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.14/2.72  tff('#skF_2', type, '#skF_2': $i).
% 7.14/2.72  tff('#skF_3', type, '#skF_3': $i).
% 7.14/2.72  tff('#skF_1', type, '#skF_1': $i).
% 7.14/2.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.14/2.72  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.14/2.72  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 7.14/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.14/2.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.14/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.14/2.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.14/2.72  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.14/2.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.14/2.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.14/2.72  
% 7.14/2.74  tff(f_85, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C))) => r1_tarski(B, k5_setfam_1(u1_struct_0(A), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_tops_2)).
% 7.14/2.74  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C)), k5_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_2)).
% 7.14/2.74  tff(f_33, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 7.14/2.74  tff(f_31, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 7.14/2.74  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.14/2.74  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.14/2.74  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.14/2.74  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.14/2.74  tff(f_35, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 7.14/2.74  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.14/2.74  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 7.14/2.74  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 7.14/2.74  tff(c_28, plain, (~r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.14/2.74  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.14/2.74  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.14/2.74  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.14/2.74  tff(c_26, plain, (![A_18, B_22, C_24]: (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_18, B_22)), k1_tops_2(A_18, B_22, C_24)), k5_setfam_1(u1_struct_0(A_18), C_24)) | ~m1_subset_1(C_24, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18)))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.14/2.74  tff(c_30, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.14/2.74  tff(c_8, plain, (![A_4]: (k3_tarski(k1_tarski(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.14/2.74  tff(c_6, plain, (![A_3]: (r1_tarski(A_3, k1_zfmisc_1(k3_tarski(A_3))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.14/2.74  tff(c_96, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | ~r1_tarski(k1_tarski(A_43), B_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.14/2.74  tff(c_110, plain, (![A_43]: (r2_hidden(A_43, k1_zfmisc_1(k3_tarski(k1_tarski(A_43)))))), inference(resolution, [status(thm)], [c_6, c_96])).
% 7.14/2.74  tff(c_115, plain, (![A_43]: (r2_hidden(A_43, k1_zfmisc_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_110])).
% 7.14/2.74  tff(c_12, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.14/2.74  tff(c_14, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.14/2.74  tff(c_37, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 7.14/2.74  tff(c_120, plain, (![C_49, B_50, A_51]: (~v1_xboole_0(C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.14/2.74  tff(c_133, plain, (![A_52, A_53]: (~v1_xboole_0(A_52) | ~r2_hidden(A_53, A_52))), inference(resolution, [status(thm)], [c_37, c_120])).
% 7.14/2.74  tff(c_145, plain, (![A_43]: (~v1_xboole_0(k1_zfmisc_1(A_43)))), inference(resolution, [status(thm)], [c_115, c_133])).
% 7.14/2.74  tff(c_10, plain, (![A_5]: (k3_tarski(k1_zfmisc_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.14/2.74  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.14/2.74  tff(c_76, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.14/2.74  tff(c_92, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(resolution, [status(thm)], [c_37, c_76])).
% 7.14/2.74  tff(c_16, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.14/2.74  tff(c_146, plain, (![C_54, B_55, A_56]: (r1_tarski(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(k3_tarski(A_56), B_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.14/2.74  tff(c_231, plain, (![A_72, B_73, B_74]: (r1_tarski(A_72, B_73) | ~r1_tarski(k3_tarski(B_74), B_73) | v1_xboole_0(B_74) | ~m1_subset_1(A_72, B_74))), inference(resolution, [status(thm)], [c_16, c_146])).
% 7.14/2.74  tff(c_246, plain, (![A_75, B_76]: (r1_tarski(A_75, k3_tarski(B_76)) | v1_xboole_0(B_76) | ~m1_subset_1(A_75, B_76))), inference(resolution, [status(thm)], [c_92, c_231])).
% 7.14/2.74  tff(c_153, plain, (![A_8, B_55, B_9]: (r1_tarski(A_8, B_55) | ~r1_tarski(k3_tarski(B_9), B_55) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(resolution, [status(thm)], [c_16, c_146])).
% 7.14/2.74  tff(c_2083, plain, (![A_222, B_223, B_224]: (r1_tarski(A_222, k3_tarski(B_223)) | v1_xboole_0(B_224) | ~m1_subset_1(A_222, B_224) | v1_xboole_0(B_223) | ~m1_subset_1(k3_tarski(B_224), B_223))), inference(resolution, [status(thm)], [c_246, c_153])).
% 7.14/2.74  tff(c_2085, plain, (![A_10, B_223, B_11]: (r1_tarski(A_10, k3_tarski(B_223)) | v1_xboole_0(k1_zfmisc_1(B_11)) | v1_xboole_0(B_223) | ~m1_subset_1(k3_tarski(k1_zfmisc_1(B_11)), B_223) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_20, c_2083])).
% 7.14/2.74  tff(c_2093, plain, (![A_10, B_223, B_11]: (r1_tarski(A_10, k3_tarski(B_223)) | v1_xboole_0(k1_zfmisc_1(B_11)) | v1_xboole_0(B_223) | ~m1_subset_1(B_11, B_223) | ~r1_tarski(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2085])).
% 7.14/2.74  tff(c_2320, plain, (![A_243, B_244, B_245]: (r1_tarski(A_243, k3_tarski(B_244)) | v1_xboole_0(B_244) | ~m1_subset_1(B_245, B_244) | ~r1_tarski(A_243, B_245))), inference(negUnitSimplification, [status(thm)], [c_145, c_2093])).
% 7.14/2.74  tff(c_2322, plain, (![A_243, B_11, A_10]: (r1_tarski(A_243, k3_tarski(k1_zfmisc_1(B_11))) | v1_xboole_0(k1_zfmisc_1(B_11)) | ~r1_tarski(A_243, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_20, c_2320])).
% 7.14/2.74  tff(c_2330, plain, (![A_243, B_11, A_10]: (r1_tarski(A_243, B_11) | v1_xboole_0(k1_zfmisc_1(B_11)) | ~r1_tarski(A_243, A_10) | ~r1_tarski(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2322])).
% 7.14/2.74  tff(c_2468, plain, (![A_250, B_251, A_252]: (r1_tarski(A_250, B_251) | ~r1_tarski(A_250, A_252) | ~r1_tarski(A_252, B_251))), inference(negUnitSimplification, [status(thm)], [c_145, c_2330])).
% 7.14/2.74  tff(c_3021, plain, (![B_266]: (r1_tarski('#skF_2', B_266) | ~r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')), B_266))), inference(resolution, [status(thm)], [c_30, c_2468])).
% 7.14/2.74  tff(c_3109, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_3021])).
% 7.14/2.74  tff(c_3150, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_3109])).
% 7.14/2.74  tff(c_3152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_3150])).
% 7.14/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.14/2.74  
% 7.14/2.74  Inference rules
% 7.14/2.74  ----------------------
% 7.14/2.74  #Ref     : 0
% 7.14/2.74  #Sup     : 727
% 7.14/2.74  #Fact    : 0
% 7.14/2.74  #Define  : 0
% 7.14/2.74  #Split   : 11
% 7.14/2.74  #Chain   : 0
% 7.14/2.74  #Close   : 0
% 7.14/2.74  
% 7.14/2.74  Ordering : KBO
% 7.14/2.74  
% 7.14/2.74  Simplification rules
% 7.14/2.74  ----------------------
% 7.14/2.74  #Subsume      : 271
% 7.14/2.74  #Demod        : 118
% 7.14/2.74  #Tautology    : 77
% 7.14/2.74  #SimpNegUnit  : 64
% 7.14/2.74  #BackRed      : 0
% 7.14/2.74  
% 7.14/2.74  #Partial instantiations: 0
% 7.14/2.74  #Strategies tried      : 1
% 7.14/2.74  
% 7.14/2.74  Timing (in seconds)
% 7.14/2.74  ----------------------
% 7.14/2.75  Preprocessing        : 0.49
% 7.14/2.75  Parsing              : 0.28
% 7.14/2.75  CNF conversion       : 0.03
% 7.14/2.75  Main loop            : 1.43
% 7.14/2.75  Inferencing          : 0.47
% 7.14/2.75  Reduction            : 0.44
% 7.14/2.75  Demodulation         : 0.29
% 7.14/2.75  BG Simplification    : 0.04
% 7.14/2.75  Subsumption          : 0.38
% 7.14/2.75  Abstraction          : 0.05
% 7.14/2.75  MUC search           : 0.00
% 7.14/2.75  Cooper               : 0.00
% 7.14/2.75  Total                : 1.98
% 7.14/2.75  Index Insertion      : 0.00
% 7.14/2.75  Index Deletion       : 0.00
% 7.14/2.75  Index Matching       : 0.00
% 7.14/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
