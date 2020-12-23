%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:06 EST 2020

% Result     : Theorem 34.57s
% Output     : CNFRefutation 34.57s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 100 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 195 expanded)
%              Number of equality atoms :   17 (  39 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_tops_2 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                   => ( r2_hidden(B,D)
                     => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),k1_tops_2(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_2)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
     => m1_subset_1(k1_tops_2(A,B,C),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B)))))
                 => ( D = k1_tops_2(A,B,C)
                  <=> ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B))))
                       => ( r2_hidden(E,D)
                        <=> ? [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(A)))
                              & r2_hidden(F,C)
                              & k9_subset_1(u1_struct_0(A),F,B) = E ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_2)).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [A_210,B_211] : k1_setfam_1(k2_tarski(A_210,B_211)) = k3_xboole_0(A_210,B_211) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_124,plain,(
    ! [B_214,A_215] : k1_setfam_1(k2_tarski(B_214,A_215)) = k3_xboole_0(A_215,B_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [B_214,A_215] : k3_xboole_0(B_214,A_215) = k3_xboole_0(A_215,B_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_8])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_160,plain,(
    ! [B_219,A_220] : k3_xboole_0(B_219,A_220) = k3_xboole_0(A_220,B_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_175,plain,(
    ! [B_219,A_220] : r1_tarski(k3_xboole_0(B_219,A_220),A_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_2])).

tff(c_304,plain,(
    ! [A_240,B_241] :
      ( u1_struct_0(k1_pre_topc(A_240,B_241)) = B_241
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_314,plain,
    ( u1_struct_0(k1_pre_topc('#skF_4','#skF_6')) = '#skF_6'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_304])).

tff(c_324,plain,(
    u1_struct_0(k1_pre_topc('#skF_4','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_314])).

tff(c_221,plain,(
    ! [A_227,B_228,C_229] :
      ( k9_subset_1(A_227,B_228,C_229) = k3_xboole_0(B_228,C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(A_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_235,plain,(
    ! [B_228] : k9_subset_1(u1_struct_0('#skF_4'),B_228,'#skF_6') = k3_xboole_0(B_228,'#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_221])).

tff(c_44,plain,(
    ! [A_190,B_191,C_192] :
      ( m1_subset_1(k1_tops_2(A_190,B_191,C_192),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_190,B_191)))))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_190))))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3424,plain,(
    ! [A_367,F_368,B_369,C_370] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_367),F_368,B_369),k1_tops_2(A_367,B_369,C_370))
      | ~ r2_hidden(F_368,C_370)
      | ~ m1_subset_1(F_368,k1_zfmisc_1(u1_struct_0(A_367)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(A_367),F_368,B_369),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_367,B_369))))
      | ~ m1_subset_1(k1_tops_2(A_367,B_369,C_370),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_367,B_369)))))
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_367))))
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0(A_367)))
      | ~ l1_pre_topc(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18884,plain,(
    ! [A_529,F_530,B_531,C_532] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_529),F_530,B_531),k1_tops_2(A_529,B_531,C_532))
      | ~ r2_hidden(F_530,C_532)
      | ~ m1_subset_1(F_530,k1_zfmisc_1(u1_struct_0(A_529)))
      | ~ m1_subset_1(k1_tops_2(A_529,B_531,C_532),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_529,B_531)))))
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_529))))
      | ~ m1_subset_1(B_531,k1_zfmisc_1(u1_struct_0(A_529)))
      | ~ l1_pre_topc(A_529)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_529),F_530,B_531),u1_struct_0(k1_pre_topc(A_529,B_531))) ) ),
    inference(resolution,[status(thm)],[c_12,c_3424])).

tff(c_60279,plain,(
    ! [A_962,F_963,B_964,C_965] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_962),F_963,B_964),k1_tops_2(A_962,B_964,C_965))
      | ~ r2_hidden(F_963,C_965)
      | ~ m1_subset_1(F_963,k1_zfmisc_1(u1_struct_0(A_962)))
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_962),F_963,B_964),u1_struct_0(k1_pre_topc(A_962,B_964)))
      | ~ m1_subset_1(C_965,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_962))))
      | ~ m1_subset_1(B_964,k1_zfmisc_1(u1_struct_0(A_962)))
      | ~ l1_pre_topc(A_962) ) ),
    inference(resolution,[status(thm)],[c_44,c_18884])).

tff(c_60365,plain,(
    ! [B_228,C_965] :
      ( r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),B_228,'#skF_6'),k1_tops_2('#skF_4','#skF_6',C_965))
      | ~ r2_hidden(B_228,C_965)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(k3_xboole_0(B_228,'#skF_6'),u1_struct_0(k1_pre_topc('#skF_4','#skF_6')))
      | ~ m1_subset_1(C_965,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_60279])).

tff(c_64026,plain,(
    ! [B_1061,C_1062] :
      ( r2_hidden(k3_xboole_0(B_1061,'#skF_6'),k1_tops_2('#skF_4','#skF_6',C_1062))
      | ~ r2_hidden(B_1061,C_1062)
      | ~ m1_subset_1(B_1061,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(C_1062,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_175,c_324,c_235,c_60365])).

tff(c_64050,plain,(
    ! [B_1063] :
      ( r2_hidden(k3_xboole_0(B_1063,'#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7'))
      | ~ r2_hidden(B_1063,'#skF_7')
      | ~ m1_subset_1(B_1063,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_50,c_64026])).

tff(c_64313,plain,(
    ! [A_1071] :
      ( r2_hidden(k3_xboole_0('#skF_6',A_1071),k1_tops_2('#skF_4','#skF_6','#skF_7'))
      | ~ r2_hidden(A_1071,'#skF_7')
      | ~ m1_subset_1(A_1071,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_64050])).

tff(c_46,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_237,plain,(
    ~ r2_hidden(k3_xboole_0('#skF_5','#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_46])).

tff(c_238,plain,(
    ~ r2_hidden(k3_xboole_0('#skF_6','#skF_5'),k1_tops_2('#skF_4','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_237])).

tff(c_64324,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_64313,c_238])).

tff(c_64379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_64324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.57/25.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.57/25.11  
% 34.57/25.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.57/25.11  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_tops_2 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4 > #skF_3
% 34.57/25.11  
% 34.57/25.11  %Foreground sorts:
% 34.57/25.11  
% 34.57/25.11  
% 34.57/25.11  %Background operators:
% 34.57/25.11  
% 34.57/25.11  
% 34.57/25.11  %Foreground operators:
% 34.57/25.11  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 34.57/25.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.57/25.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 34.57/25.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 34.57/25.11  tff('#skF_7', type, '#skF_7': $i).
% 34.57/25.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 34.57/25.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 34.57/25.11  tff('#skF_5', type, '#skF_5': $i).
% 34.57/25.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 34.57/25.11  tff('#skF_6', type, '#skF_6': $i).
% 34.57/25.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 34.57/25.11  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 34.57/25.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 34.57/25.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.57/25.11  tff('#skF_4', type, '#skF_4': $i).
% 34.57/25.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.57/25.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 34.57/25.11  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 34.57/25.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 34.57/25.11  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 34.57/25.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 34.57/25.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 34.57/25.11  
% 34.57/25.12  tff(f_101, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r2_hidden(B, D) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), k1_tops_2(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_2)).
% 34.57/25.12  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 34.57/25.12  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 34.57/25.12  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 34.57/25.12  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 34.57/25.12  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 34.57/25.12  tff(f_85, axiom, (![A, B, C]: (((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) => m1_subset_1(k1_tops_2(A, B, C), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 34.57/25.12  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 34.57/25.12  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B))))) => ((D = k1_tops_2(A, B, C)) <=> (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B)))) => (r2_hidden(E, D) <=> (?[F]: ((m1_subset_1(F, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(F, C)) & (k9_subset_1(u1_struct_0(A), F, B) = E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_2)).
% 34.57/25.12  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 34.57/25.12  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_101])).
% 34.57/25.12  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 34.57/25.12  tff(c_92, plain, (![A_210, B_211]: (k1_setfam_1(k2_tarski(A_210, B_211))=k3_xboole_0(A_210, B_211))), inference(cnfTransformation, [status(thm)], [f_35])).
% 34.57/25.12  tff(c_124, plain, (![B_214, A_215]: (k1_setfam_1(k2_tarski(B_214, A_215))=k3_xboole_0(A_215, B_214))), inference(superposition, [status(thm), theory('equality')], [c_4, c_92])).
% 34.57/25.12  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 34.57/25.12  tff(c_130, plain, (![B_214, A_215]: (k3_xboole_0(B_214, A_215)=k3_xboole_0(A_215, B_214))), inference(superposition, [status(thm), theory('equality')], [c_124, c_8])).
% 34.57/25.12  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 34.57/25.12  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 34.57/25.12  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 34.57/25.12  tff(c_160, plain, (![B_219, A_220]: (k3_xboole_0(B_219, A_220)=k3_xboole_0(A_220, B_219))), inference(superposition, [status(thm), theory('equality')], [c_124, c_8])).
% 34.57/25.12  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 34.57/25.12  tff(c_175, plain, (![B_219, A_220]: (r1_tarski(k3_xboole_0(B_219, A_220), A_220))), inference(superposition, [status(thm), theory('equality')], [c_160, c_2])).
% 34.57/25.12  tff(c_304, plain, (![A_240, B_241]: (u1_struct_0(k1_pre_topc(A_240, B_241))=B_241 | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_52])).
% 34.57/25.12  tff(c_314, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_6'))='#skF_6' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_304])).
% 34.57/25.12  tff(c_324, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_314])).
% 34.57/25.12  tff(c_221, plain, (![A_227, B_228, C_229]: (k9_subset_1(A_227, B_228, C_229)=k3_xboole_0(B_228, C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(A_227)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 34.57/25.12  tff(c_235, plain, (![B_228]: (k9_subset_1(u1_struct_0('#skF_4'), B_228, '#skF_6')=k3_xboole_0(B_228, '#skF_6'))), inference(resolution, [status(thm)], [c_52, c_221])).
% 34.57/25.12  tff(c_44, plain, (![A_190, B_191, C_192]: (m1_subset_1(k1_tops_2(A_190, B_191, C_192), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_190, B_191))))) | ~m1_subset_1(C_192, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_190)))) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_85])).
% 34.57/25.12  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 34.57/25.12  tff(c_3424, plain, (![A_367, F_368, B_369, C_370]: (r2_hidden(k9_subset_1(u1_struct_0(A_367), F_368, B_369), k1_tops_2(A_367, B_369, C_370)) | ~r2_hidden(F_368, C_370) | ~m1_subset_1(F_368, k1_zfmisc_1(u1_struct_0(A_367))) | ~m1_subset_1(k9_subset_1(u1_struct_0(A_367), F_368, B_369), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_367, B_369)))) | ~m1_subset_1(k1_tops_2(A_367, B_369, C_370), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_367, B_369))))) | ~m1_subset_1(C_370, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_367)))) | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0(A_367))) | ~l1_pre_topc(A_367))), inference(cnfTransformation, [status(thm)], [f_77])).
% 34.57/25.12  tff(c_18884, plain, (![A_529, F_530, B_531, C_532]: (r2_hidden(k9_subset_1(u1_struct_0(A_529), F_530, B_531), k1_tops_2(A_529, B_531, C_532)) | ~r2_hidden(F_530, C_532) | ~m1_subset_1(F_530, k1_zfmisc_1(u1_struct_0(A_529))) | ~m1_subset_1(k1_tops_2(A_529, B_531, C_532), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_529, B_531))))) | ~m1_subset_1(C_532, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_529)))) | ~m1_subset_1(B_531, k1_zfmisc_1(u1_struct_0(A_529))) | ~l1_pre_topc(A_529) | ~r1_tarski(k9_subset_1(u1_struct_0(A_529), F_530, B_531), u1_struct_0(k1_pre_topc(A_529, B_531))))), inference(resolution, [status(thm)], [c_12, c_3424])).
% 34.57/25.12  tff(c_60279, plain, (![A_962, F_963, B_964, C_965]: (r2_hidden(k9_subset_1(u1_struct_0(A_962), F_963, B_964), k1_tops_2(A_962, B_964, C_965)) | ~r2_hidden(F_963, C_965) | ~m1_subset_1(F_963, k1_zfmisc_1(u1_struct_0(A_962))) | ~r1_tarski(k9_subset_1(u1_struct_0(A_962), F_963, B_964), u1_struct_0(k1_pre_topc(A_962, B_964))) | ~m1_subset_1(C_965, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_962)))) | ~m1_subset_1(B_964, k1_zfmisc_1(u1_struct_0(A_962))) | ~l1_pre_topc(A_962))), inference(resolution, [status(thm)], [c_44, c_18884])).
% 34.57/25.12  tff(c_60365, plain, (![B_228, C_965]: (r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), B_228, '#skF_6'), k1_tops_2('#skF_4', '#skF_6', C_965)) | ~r2_hidden(B_228, C_965) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(k3_xboole_0(B_228, '#skF_6'), u1_struct_0(k1_pre_topc('#skF_4', '#skF_6'))) | ~m1_subset_1(C_965, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_60279])).
% 34.57/25.12  tff(c_64026, plain, (![B_1061, C_1062]: (r2_hidden(k3_xboole_0(B_1061, '#skF_6'), k1_tops_2('#skF_4', '#skF_6', C_1062)) | ~r2_hidden(B_1061, C_1062) | ~m1_subset_1(B_1061, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(C_1062, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_175, c_324, c_235, c_60365])).
% 34.57/25.12  tff(c_64050, plain, (![B_1063]: (r2_hidden(k3_xboole_0(B_1063, '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7')) | ~r2_hidden(B_1063, '#skF_7') | ~m1_subset_1(B_1063, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_50, c_64026])).
% 34.57/25.12  tff(c_64313, plain, (![A_1071]: (r2_hidden(k3_xboole_0('#skF_6', A_1071), k1_tops_2('#skF_4', '#skF_6', '#skF_7')) | ~r2_hidden(A_1071, '#skF_7') | ~m1_subset_1(A_1071, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_130, c_64050])).
% 34.57/25.12  tff(c_46, plain, (~r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 34.57/25.12  tff(c_237, plain, (~r2_hidden(k3_xboole_0('#skF_5', '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_46])).
% 34.57/25.12  tff(c_238, plain, (~r2_hidden(k3_xboole_0('#skF_6', '#skF_5'), k1_tops_2('#skF_4', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_237])).
% 34.57/25.12  tff(c_64324, plain, (~r2_hidden('#skF_5', '#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_64313, c_238])).
% 34.57/25.12  tff(c_64379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_64324])).
% 34.57/25.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.57/25.12  
% 34.57/25.12  Inference rules
% 34.57/25.12  ----------------------
% 34.57/25.12  #Ref     : 0
% 34.57/25.12  #Sup     : 17643
% 34.57/25.12  #Fact    : 0
% 34.57/25.12  #Define  : 0
% 34.57/25.12  #Split   : 5
% 34.57/25.12  #Chain   : 0
% 34.57/25.12  #Close   : 0
% 34.57/25.12  
% 34.57/25.12  Ordering : KBO
% 34.57/25.12  
% 34.57/25.12  Simplification rules
% 34.57/25.12  ----------------------
% 34.57/25.12  #Subsume      : 1227
% 34.57/25.12  #Demod        : 4404
% 34.57/25.12  #Tautology    : 3075
% 34.57/25.12  #SimpNegUnit  : 0
% 34.57/25.12  #BackRed      : 1
% 34.57/25.13  
% 34.57/25.13  #Partial instantiations: 0
% 34.57/25.13  #Strategies tried      : 1
% 34.57/25.13  
% 34.57/25.13  Timing (in seconds)
% 34.57/25.13  ----------------------
% 34.57/25.13  Preprocessing        : 0.34
% 34.57/25.13  Parsing              : 0.16
% 34.57/25.13  CNF conversion       : 0.04
% 34.57/25.13  Main loop            : 24.00
% 34.57/25.13  Inferencing          : 2.22
% 34.57/25.13  Reduction            : 18.18
% 34.57/25.13  Demodulation         : 17.62
% 34.57/25.13  BG Simplification    : 0.42
% 34.57/25.13  Subsumption          : 2.46
% 34.57/25.13  Abstraction          : 0.47
% 34.57/25.13  MUC search           : 0.00
% 34.57/25.13  Cooper               : 0.00
% 34.57/25.13  Total                : 24.37
% 34.57/25.13  Index Insertion      : 0.00
% 34.57/25.13  Index Deletion       : 0.00
% 34.57/25.13  Index Matching       : 0.00
% 34.57/25.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
