%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:06 EST 2020

% Result     : Theorem 21.50s
% Output     : CNFRefutation 21.50s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 186 expanded)
%              Number of leaves         :   28 (  78 expanded)
%              Depth                    :   17
%              Number of atoms          :  134 ( 458 expanded)
%              Number of equality atoms :   14 (  45 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_tops_2 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4 > #skF_3

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_105,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_2)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
     => m1_subset_1(k1_tops_2(A,B,C),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_144,plain,(
    ! [A_221,B_222,C_223] :
      ( k9_subset_1(A_221,B_222,C_223) = k3_xboole_0(B_222,C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(A_221)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_190,plain,(
    ! [B_227,B_228,A_229] :
      ( k9_subset_1(B_227,B_228,A_229) = k3_xboole_0(B_228,A_229)
      | ~ r1_tarski(A_229,B_227) ) ),
    inference(resolution,[status(thm)],[c_14,c_144])).

tff(c_208,plain,(
    ! [B_2,B_228] : k9_subset_1(B_2,B_228,B_2) = k3_xboole_0(B_228,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_190])).

tff(c_209,plain,(
    ! [A_230,B_231,C_232] :
      ( m1_subset_1(k9_subset_1(A_230,B_231,C_232),k1_zfmisc_1(A_230))
      | ~ m1_subset_1(C_232,k1_zfmisc_1(A_230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_478,plain,(
    ! [A_254,B_255,C_256] :
      ( r1_tarski(k9_subset_1(A_254,B_255,C_256),A_254)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(A_254)) ) ),
    inference(resolution,[status(thm)],[c_209,c_12])).

tff(c_488,plain,(
    ! [B_228,B_2] :
      ( r1_tarski(k3_xboole_0(B_228,B_2),B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_478])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_306,plain,(
    ! [A_245,B_246] :
      ( u1_struct_0(k1_pre_topc(A_245,B_246)) = B_246
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_326,plain,
    ( u1_struct_0(k1_pre_topc('#skF_4','#skF_6')) = '#skF_6'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_306])).

tff(c_343,plain,(
    u1_struct_0(k1_pre_topc('#skF_4','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_326])).

tff(c_513,plain,(
    ! [A_259,B_260,C_261] :
      ( m1_subset_1(k1_tops_2(A_259,B_260,C_261),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_259,B_260)))))
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_259))))
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_535,plain,(
    ! [C_261] :
      ( m1_subset_1(k1_tops_2('#skF_4','#skF_6',C_261),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_513])).

tff(c_548,plain,(
    ! [C_261] :
      ( m1_subset_1(k1_tops_2('#skF_4','#skF_6',C_261),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_535])).

tff(c_1305,plain,(
    ! [C_342] :
      ( m1_subset_1(k1_tops_2('#skF_4','#skF_6',C_342),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_535])).

tff(c_1316,plain,(
    ! [C_343] :
      ( r1_tarski(k1_tops_2('#skF_4','#skF_6',C_343),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(resolution,[status(thm)],[c_1305,c_12])).

tff(c_1343,plain,(
    r1_tarski(k1_tops_2('#skF_4','#skF_6','#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_1316])).

tff(c_156,plain,(
    ! [B_10,B_222,A_9] :
      ( k9_subset_1(B_10,B_222,A_9) = k3_xboole_0(B_222,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_144])).

tff(c_1410,plain,(
    ! [B_352] : k9_subset_1(k1_zfmisc_1('#skF_6'),B_352,k1_tops_2('#skF_4','#skF_6','#skF_7')) = k3_xboole_0(B_352,k1_tops_2('#skF_4','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1343,c_156])).

tff(c_228,plain,(
    ! [A_230,B_231,C_232] :
      ( r1_tarski(k9_subset_1(A_230,B_231,C_232),A_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(A_230)) ) ),
    inference(resolution,[status(thm)],[c_209,c_12])).

tff(c_1419,plain,(
    ! [B_352] :
      ( r1_tarski(k3_xboole_0(B_352,k1_tops_2('#skF_4','#skF_6','#skF_7')),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(k1_tops_2('#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1410,c_228])).

tff(c_1994,plain,(
    ~ m1_subset_1(k1_tops_2('#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1419])).

tff(c_1997,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_548,c_1994])).

tff(c_2004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1997])).

tff(c_2006,plain,(
    m1_subset_1(k1_tops_2('#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1419])).

tff(c_158,plain,(
    ! [B_222] : k9_subset_1(u1_struct_0('#skF_4'),B_222,'#skF_6') = k3_xboole_0(B_222,'#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_144])).

tff(c_2108,plain,(
    ! [A_438,F_439,B_440,C_441] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_438),F_439,B_440),k1_tops_2(A_438,B_440,C_441))
      | ~ r2_hidden(F_439,C_441)
      | ~ m1_subset_1(F_439,k1_zfmisc_1(u1_struct_0(A_438)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(A_438),F_439,B_440),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_438,B_440))))
      | ~ m1_subset_1(k1_tops_2(A_438,B_440,C_441),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_438,B_440)))))
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_438))))
      | ~ m1_subset_1(B_440,k1_zfmisc_1(u1_struct_0(A_438)))
      | ~ l1_pre_topc(A_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9016,plain,(
    ! [A_819,F_820,B_821,C_822] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_819),F_820,B_821),k1_tops_2(A_819,B_821,C_822))
      | ~ r2_hidden(F_820,C_822)
      | ~ m1_subset_1(F_820,k1_zfmisc_1(u1_struct_0(A_819)))
      | ~ m1_subset_1(k1_tops_2(A_819,B_821,C_822),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_819,B_821)))))
      | ~ m1_subset_1(C_822,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_819))))
      | ~ m1_subset_1(B_821,k1_zfmisc_1(u1_struct_0(A_819)))
      | ~ l1_pre_topc(A_819)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_819),F_820,B_821),u1_struct_0(k1_pre_topc(A_819,B_821))) ) ),
    inference(resolution,[status(thm)],[c_14,c_2108])).

tff(c_9066,plain,(
    ! [F_820,C_822] :
      ( r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),F_820,'#skF_6'),k1_tops_2('#skF_4','#skF_6',C_822))
      | ~ r2_hidden(F_820,C_822)
      | ~ m1_subset_1(F_820,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k1_tops_2('#skF_4','#skF_6',C_822),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1(C_822,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),F_820,'#skF_6'),u1_struct_0(k1_pre_topc('#skF_4','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_9016])).

tff(c_27448,plain,(
    ! [F_1393,C_1394] :
      ( r2_hidden(k3_xboole_0(F_1393,'#skF_6'),k1_tops_2('#skF_4','#skF_6',C_1394))
      | ~ r2_hidden(F_1393,C_1394)
      | ~ m1_subset_1(F_1393,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k1_tops_2('#skF_4','#skF_6',C_1394),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1(C_1394,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ r1_tarski(k3_xboole_0(F_1393,'#skF_6'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_343,c_58,c_54,c_158,c_9066])).

tff(c_27455,plain,(
    ! [F_1393] :
      ( r2_hidden(k3_xboole_0(F_1393,'#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7'))
      | ~ r2_hidden(F_1393,'#skF_7')
      | ~ m1_subset_1(F_1393,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ r1_tarski(k3_xboole_0(F_1393,'#skF_6'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2006,c_27448])).

tff(c_28706,plain,(
    ! [F_1430] :
      ( r2_hidden(k3_xboole_0(F_1430,'#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7'))
      | ~ r2_hidden(F_1430,'#skF_7')
      | ~ m1_subset_1(F_1430,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(k3_xboole_0(F_1430,'#skF_6'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_27455])).

tff(c_48,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_161,plain,(
    ~ r2_hidden(k3_xboole_0('#skF_5','#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_48])).

tff(c_28730,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_28706,c_161])).

tff(c_28754,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_28730])).

tff(c_28759,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_488,c_28754])).

tff(c_28762,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_28759])).

tff(c_28766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28762])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.50/10.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.50/10.81  
% 21.50/10.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.50/10.81  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_tops_2 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4 > #skF_3
% 21.50/10.81  
% 21.50/10.81  %Foreground sorts:
% 21.50/10.81  
% 21.50/10.81  
% 21.50/10.81  %Background operators:
% 21.50/10.81  
% 21.50/10.81  
% 21.50/10.81  %Foreground operators:
% 21.50/10.81  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 21.50/10.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.50/10.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.50/10.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.50/10.81  tff('#skF_7', type, '#skF_7': $i).
% 21.50/10.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.50/10.81  tff('#skF_5', type, '#skF_5': $i).
% 21.50/10.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 21.50/10.81  tff('#skF_6', type, '#skF_6': $i).
% 21.50/10.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.50/10.81  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 21.50/10.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 21.50/10.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.50/10.81  tff('#skF_4', type, '#skF_4': $i).
% 21.50/10.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.50/10.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.50/10.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 21.50/10.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.50/10.81  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 21.50/10.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.50/10.81  
% 21.50/10.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.50/10.83  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 21.50/10.83  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 21.50/10.83  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 21.50/10.83  tff(f_105, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r2_hidden(B, D) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), k1_tops_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_2)).
% 21.50/10.83  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 21.50/10.83  tff(f_89, axiom, (![A, B, C]: (((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) => m1_subset_1(k1_tops_2(A, B, C), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 21.50/10.83  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B))))) => ((D = k1_tops_2(A, B, C)) <=> (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B)))) => (r2_hidden(E, D) <=> (?[F]: ((m1_subset_1(F, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(F, C)) & (k9_subset_1(u1_struct_0(A), F, B) = E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_2)).
% 21.50/10.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.50/10.83  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.50/10.83  tff(c_144, plain, (![A_221, B_222, C_223]: (k9_subset_1(A_221, B_222, C_223)=k3_xboole_0(B_222, C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(A_221)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.50/10.83  tff(c_190, plain, (![B_227, B_228, A_229]: (k9_subset_1(B_227, B_228, A_229)=k3_xboole_0(B_228, A_229) | ~r1_tarski(A_229, B_227))), inference(resolution, [status(thm)], [c_14, c_144])).
% 21.50/10.83  tff(c_208, plain, (![B_2, B_228]: (k9_subset_1(B_2, B_228, B_2)=k3_xboole_0(B_228, B_2))), inference(resolution, [status(thm)], [c_6, c_190])).
% 21.50/10.83  tff(c_209, plain, (![A_230, B_231, C_232]: (m1_subset_1(k9_subset_1(A_230, B_231, C_232), k1_zfmisc_1(A_230)) | ~m1_subset_1(C_232, k1_zfmisc_1(A_230)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.50/10.83  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.50/10.83  tff(c_478, plain, (![A_254, B_255, C_256]: (r1_tarski(k9_subset_1(A_254, B_255, C_256), A_254) | ~m1_subset_1(C_256, k1_zfmisc_1(A_254)))), inference(resolution, [status(thm)], [c_209, c_12])).
% 21.50/10.83  tff(c_488, plain, (![B_228, B_2]: (r1_tarski(k3_xboole_0(B_228, B_2), B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_208, c_478])).
% 21.50/10.83  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 21.50/10.83  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_105])).
% 21.50/10.83  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 21.50/10.83  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 21.50/10.83  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 21.50/10.83  tff(c_306, plain, (![A_245, B_246]: (u1_struct_0(k1_pre_topc(A_245, B_246))=B_246 | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_56])).
% 21.50/10.83  tff(c_326, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_6'))='#skF_6' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_306])).
% 21.50/10.83  tff(c_343, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_326])).
% 21.50/10.83  tff(c_513, plain, (![A_259, B_260, C_261]: (m1_subset_1(k1_tops_2(A_259, B_260, C_261), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_259, B_260))))) | ~m1_subset_1(C_261, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_259)))) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.50/10.83  tff(c_535, plain, (![C_261]: (m1_subset_1(k1_tops_2('#skF_4', '#skF_6', C_261), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1(C_261, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_343, c_513])).
% 21.50/10.83  tff(c_548, plain, (![C_261]: (m1_subset_1(k1_tops_2('#skF_4', '#skF_6', C_261), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1(C_261, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_535])).
% 21.50/10.83  tff(c_1305, plain, (![C_342]: (m1_subset_1(k1_tops_2('#skF_4', '#skF_6', C_342), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1(C_342, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_535])).
% 21.50/10.83  tff(c_1316, plain, (![C_343]: (r1_tarski(k1_tops_2('#skF_4', '#skF_6', C_343), k1_zfmisc_1('#skF_6')) | ~m1_subset_1(C_343, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(resolution, [status(thm)], [c_1305, c_12])).
% 21.50/10.83  tff(c_1343, plain, (r1_tarski(k1_tops_2('#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_1316])).
% 21.50/10.83  tff(c_156, plain, (![B_10, B_222, A_9]: (k9_subset_1(B_10, B_222, A_9)=k3_xboole_0(B_222, A_9) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_14, c_144])).
% 21.50/10.83  tff(c_1410, plain, (![B_352]: (k9_subset_1(k1_zfmisc_1('#skF_6'), B_352, k1_tops_2('#skF_4', '#skF_6', '#skF_7'))=k3_xboole_0(B_352, k1_tops_2('#skF_4', '#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_1343, c_156])).
% 21.50/10.83  tff(c_228, plain, (![A_230, B_231, C_232]: (r1_tarski(k9_subset_1(A_230, B_231, C_232), A_230) | ~m1_subset_1(C_232, k1_zfmisc_1(A_230)))), inference(resolution, [status(thm)], [c_209, c_12])).
% 21.50/10.83  tff(c_1419, plain, (![B_352]: (r1_tarski(k3_xboole_0(B_352, k1_tops_2('#skF_4', '#skF_6', '#skF_7')), k1_zfmisc_1('#skF_6')) | ~m1_subset_1(k1_tops_2('#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_1410, c_228])).
% 21.50/10.83  tff(c_1994, plain, (~m1_subset_1(k1_tops_2('#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_1419])).
% 21.50/10.83  tff(c_1997, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_548, c_1994])).
% 21.50/10.83  tff(c_2004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1997])).
% 21.50/10.83  tff(c_2006, plain, (m1_subset_1(k1_tops_2('#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_1419])).
% 21.50/10.83  tff(c_158, plain, (![B_222]: (k9_subset_1(u1_struct_0('#skF_4'), B_222, '#skF_6')=k3_xboole_0(B_222, '#skF_6'))), inference(resolution, [status(thm)], [c_54, c_144])).
% 21.50/10.83  tff(c_2108, plain, (![A_438, F_439, B_440, C_441]: (r2_hidden(k9_subset_1(u1_struct_0(A_438), F_439, B_440), k1_tops_2(A_438, B_440, C_441)) | ~r2_hidden(F_439, C_441) | ~m1_subset_1(F_439, k1_zfmisc_1(u1_struct_0(A_438))) | ~m1_subset_1(k9_subset_1(u1_struct_0(A_438), F_439, B_440), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_438, B_440)))) | ~m1_subset_1(k1_tops_2(A_438, B_440, C_441), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_438, B_440))))) | ~m1_subset_1(C_441, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_438)))) | ~m1_subset_1(B_440, k1_zfmisc_1(u1_struct_0(A_438))) | ~l1_pre_topc(A_438))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.50/10.83  tff(c_9016, plain, (![A_819, F_820, B_821, C_822]: (r2_hidden(k9_subset_1(u1_struct_0(A_819), F_820, B_821), k1_tops_2(A_819, B_821, C_822)) | ~r2_hidden(F_820, C_822) | ~m1_subset_1(F_820, k1_zfmisc_1(u1_struct_0(A_819))) | ~m1_subset_1(k1_tops_2(A_819, B_821, C_822), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_819, B_821))))) | ~m1_subset_1(C_822, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_819)))) | ~m1_subset_1(B_821, k1_zfmisc_1(u1_struct_0(A_819))) | ~l1_pre_topc(A_819) | ~r1_tarski(k9_subset_1(u1_struct_0(A_819), F_820, B_821), u1_struct_0(k1_pre_topc(A_819, B_821))))), inference(resolution, [status(thm)], [c_14, c_2108])).
% 21.50/10.83  tff(c_9066, plain, (![F_820, C_822]: (r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), F_820, '#skF_6'), k1_tops_2('#skF_4', '#skF_6', C_822)) | ~r2_hidden(F_820, C_822) | ~m1_subset_1(F_820, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_tops_2('#skF_4', '#skF_6', C_822), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1(C_822, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), F_820, '#skF_6'), u1_struct_0(k1_pre_topc('#skF_4', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_343, c_9016])).
% 21.50/10.83  tff(c_27448, plain, (![F_1393, C_1394]: (r2_hidden(k3_xboole_0(F_1393, '#skF_6'), k1_tops_2('#skF_4', '#skF_6', C_1394)) | ~r2_hidden(F_1393, C_1394) | ~m1_subset_1(F_1393, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_tops_2('#skF_4', '#skF_6', C_1394), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1(C_1394, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~r1_tarski(k3_xboole_0(F_1393, '#skF_6'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_343, c_58, c_54, c_158, c_9066])).
% 21.50/10.83  tff(c_27455, plain, (![F_1393]: (r2_hidden(k3_xboole_0(F_1393, '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7')) | ~r2_hidden(F_1393, '#skF_7') | ~m1_subset_1(F_1393, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~r1_tarski(k3_xboole_0(F_1393, '#skF_6'), '#skF_6'))), inference(resolution, [status(thm)], [c_2006, c_27448])).
% 21.50/10.83  tff(c_28706, plain, (![F_1430]: (r2_hidden(k3_xboole_0(F_1430, '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7')) | ~r2_hidden(F_1430, '#skF_7') | ~m1_subset_1(F_1430, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(k3_xboole_0(F_1430, '#skF_6'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_27455])).
% 21.50/10.83  tff(c_48, plain, (~r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 21.50/10.83  tff(c_161, plain, (~r2_hidden(k3_xboole_0('#skF_5', '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_48])).
% 21.50/10.83  tff(c_28730, plain, (~r2_hidden('#skF_5', '#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_28706, c_161])).
% 21.50/10.83  tff(c_28754, plain, (~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_28730])).
% 21.50/10.83  tff(c_28759, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_488, c_28754])).
% 21.50/10.83  tff(c_28762, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_14, c_28759])).
% 21.50/10.83  tff(c_28766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_28762])).
% 21.50/10.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.50/10.83  
% 21.50/10.83  Inference rules
% 21.50/10.83  ----------------------
% 21.50/10.83  #Ref     : 0
% 21.50/10.83  #Sup     : 7228
% 21.50/10.83  #Fact    : 0
% 21.50/10.83  #Define  : 0
% 21.50/10.83  #Split   : 30
% 21.50/10.83  #Chain   : 0
% 21.50/10.83  #Close   : 0
% 21.50/10.83  
% 21.50/10.83  Ordering : KBO
% 21.50/10.83  
% 21.50/10.83  Simplification rules
% 21.50/10.83  ----------------------
% 21.50/10.83  #Subsume      : 550
% 21.50/10.83  #Demod        : 6277
% 21.50/10.83  #Tautology    : 1175
% 21.50/10.83  #SimpNegUnit  : 20
% 21.50/10.83  #BackRed      : 97
% 21.50/10.83  
% 21.50/10.83  #Partial instantiations: 0
% 21.50/10.83  #Strategies tried      : 1
% 21.50/10.83  
% 21.50/10.83  Timing (in seconds)
% 21.50/10.83  ----------------------
% 21.50/10.83  Preprocessing        : 0.36
% 21.50/10.83  Parsing              : 0.17
% 21.50/10.83  CNF conversion       : 0.04
% 21.50/10.83  Main loop            : 9.69
% 21.50/10.83  Inferencing          : 1.72
% 21.50/10.83  Reduction            : 4.61
% 21.50/10.83  Demodulation         : 3.90
% 21.50/10.83  BG Simplification    : 0.30
% 21.50/10.83  Subsumption          : 2.54
% 21.50/10.83  Abstraction          : 0.45
% 21.50/10.83  MUC search           : 0.00
% 21.50/10.83  Cooper               : 0.00
% 21.50/10.83  Total                : 10.08
% 21.50/10.83  Index Insertion      : 0.00
% 21.50/10.83  Index Deletion       : 0.00
% 21.50/10.83  Index Matching       : 0.00
% 21.50/10.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
