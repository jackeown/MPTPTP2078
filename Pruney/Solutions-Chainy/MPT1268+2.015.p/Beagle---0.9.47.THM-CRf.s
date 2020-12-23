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
% DateTime   : Thu Dec  3 10:21:48 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 127 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  157 ( 373 expanded)
%              Number of equality atoms :   21 (  50 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_36,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_252,plain,(
    ! [B_69,A_70] :
      ( v2_tops_1(B_69,A_70)
      | k1_tops_1(A_70,B_69) != k1_xboole_0
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_259,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_252])).

tff(c_263,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_259])).

tff(c_264,plain,(
    k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_263])).

tff(c_118,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tops_1(A_53,B_54),B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_123,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_118])).

tff(c_127,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_123])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_131,plain,(
    ! [A_55,B_56] :
      ( v3_pre_topc(k1_tops_1(A_55,B_56),A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_136,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_131])).

tff(c_140,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_136])).

tff(c_59,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_50,B_51,B_52] :
      ( r2_hidden('#skF_1'(A_50,B_51),B_52)
      | ~ r1_tarski(A_50,B_52)
      | r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_294,plain,(
    ! [A_75,B_76,B_77,B_78] :
      ( r2_hidden('#skF_1'(A_75,B_76),B_77)
      | ~ r1_tarski(B_78,B_77)
      | ~ r1_tarski(A_75,B_78)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_395,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_89,'#skF_3')
      | r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_63,c_294])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_404,plain,(
    ! [A_91] :
      ( ~ r1_tarski(A_91,'#skF_3')
      | r1_tarski(A_91,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_395,c_4])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    ! [C_33] :
      ( v2_tops_1('#skF_3','#skF_2')
      | k1_xboole_0 = C_33
      | ~ v3_pre_topc(C_33,'#skF_2')
      | ~ r1_tarski(C_33,'#skF_3')
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_191,plain,(
    ! [C_64] :
      ( k1_xboole_0 = C_64
      | ~ v3_pre_topc(C_64,'#skF_2')
      | ~ r1_tarski(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54])).

tff(c_199,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v3_pre_topc(A_9,'#skF_2')
      | ~ r1_tarski(A_9,'#skF_3')
      | ~ r1_tarski(A_9,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_18,c_191])).

tff(c_445,plain,(
    ! [A_93] :
      ( k1_xboole_0 = A_93
      | ~ v3_pre_topc(A_93,'#skF_2')
      | ~ r1_tarski(A_93,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_404,c_199])).

tff(c_455,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_445])).

tff(c_465,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_455])).

tff(c_467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_465])).

tff(c_468,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_469,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_471,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_38])).

tff(c_40,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_473,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_40])).

tff(c_42,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_480,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_42])).

tff(c_636,plain,(
    ! [A_122,B_123] :
      ( k1_tops_1(A_122,B_123) = k1_xboole_0
      | ~ v2_tops_1(B_123,A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_646,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_636])).

tff(c_653,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469,c_646])).

tff(c_861,plain,(
    ! [B_144,A_145,C_146] :
      ( r1_tarski(B_144,k1_tops_1(A_145,C_146))
      | ~ r1_tarski(B_144,C_146)
      | ~ v3_pre_topc(B_144,A_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_868,plain,(
    ! [B_144] :
      ( r1_tarski(B_144,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_144,'#skF_3')
      | ~ v3_pre_topc(B_144,'#skF_2')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_861])).

tff(c_927,plain,(
    ! [B_153] :
      ( r1_tarski(B_153,k1_xboole_0)
      | ~ r1_tarski(B_153,'#skF_3')
      | ~ v3_pre_topc(B_153,'#skF_2')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_653,c_868])).

tff(c_934,plain,
    ( r1_tarski('#skF_4',k1_xboole_0)
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_480,c_927])).

tff(c_941,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_473,c_934])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_498,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ r1_tarski(B_102,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_516,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_498])).

tff(c_952,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_941,c_516])).

tff(c_960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_468,c_952])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:11:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.46  
% 3.32/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.47  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.32/1.47  
% 3.32/1.47  %Foreground sorts:
% 3.32/1.47  
% 3.32/1.47  
% 3.32/1.47  %Background operators:
% 3.32/1.47  
% 3.32/1.47  
% 3.32/1.47  %Foreground operators:
% 3.32/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.32/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.47  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.32/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.32/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.32/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.32/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.47  
% 3.32/1.48  tff(f_101, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 3.32/1.48  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.32/1.48  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.32/1.48  tff(f_52, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.32/1.48  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.32/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.32/1.48  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.32/1.48  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.32/1.48  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.32/1.48  tff(c_36, plain, (k1_xboole_0!='#skF_4' | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.48  tff(c_58, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 3.32/1.48  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.48  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.48  tff(c_252, plain, (![B_69, A_70]: (v2_tops_1(B_69, A_70) | k1_tops_1(A_70, B_69)!=k1_xboole_0 | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.32/1.48  tff(c_259, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_252])).
% 3.32/1.48  tff(c_263, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_259])).
% 3.32/1.48  tff(c_264, plain, (k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_263])).
% 3.32/1.48  tff(c_118, plain, (![A_53, B_54]: (r1_tarski(k1_tops_1(A_53, B_54), B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.32/1.48  tff(c_123, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_118])).
% 3.32/1.48  tff(c_127, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_123])).
% 3.32/1.48  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.48  tff(c_131, plain, (![A_55, B_56]: (v3_pre_topc(k1_tops_1(A_55, B_56), A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.32/1.48  tff(c_136, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_131])).
% 3.32/1.48  tff(c_140, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_136])).
% 3.32/1.48  tff(c_59, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.32/1.48  tff(c_63, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_59])).
% 3.32/1.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.48  tff(c_105, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.48  tff(c_109, plain, (![A_50, B_51, B_52]: (r2_hidden('#skF_1'(A_50, B_51), B_52) | ~r1_tarski(A_50, B_52) | r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_6, c_105])).
% 3.32/1.48  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.48  tff(c_294, plain, (![A_75, B_76, B_77, B_78]: (r2_hidden('#skF_1'(A_75, B_76), B_77) | ~r1_tarski(B_78, B_77) | ~r1_tarski(A_75, B_78) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_109, c_2])).
% 3.32/1.48  tff(c_395, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), u1_struct_0('#skF_2')) | ~r1_tarski(A_89, '#skF_3') | r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_63, c_294])).
% 3.32/1.48  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.48  tff(c_404, plain, (![A_91]: (~r1_tarski(A_91, '#skF_3') | r1_tarski(A_91, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_395, c_4])).
% 3.32/1.48  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.32/1.48  tff(c_54, plain, (![C_33]: (v2_tops_1('#skF_3', '#skF_2') | k1_xboole_0=C_33 | ~v3_pre_topc(C_33, '#skF_2') | ~r1_tarski(C_33, '#skF_3') | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.48  tff(c_191, plain, (![C_64]: (k1_xboole_0=C_64 | ~v3_pre_topc(C_64, '#skF_2') | ~r1_tarski(C_64, '#skF_3') | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_54])).
% 3.32/1.48  tff(c_199, plain, (![A_9]: (k1_xboole_0=A_9 | ~v3_pre_topc(A_9, '#skF_2') | ~r1_tarski(A_9, '#skF_3') | ~r1_tarski(A_9, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_18, c_191])).
% 3.32/1.48  tff(c_445, plain, (![A_93]: (k1_xboole_0=A_93 | ~v3_pre_topc(A_93, '#skF_2') | ~r1_tarski(A_93, '#skF_3'))), inference(resolution, [status(thm)], [c_404, c_199])).
% 3.32/1.48  tff(c_455, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_140, c_445])).
% 3.32/1.48  tff(c_465, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_127, c_455])).
% 3.32/1.48  tff(c_467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_264, c_465])).
% 3.32/1.48  tff(c_468, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 3.32/1.48  tff(c_469, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 3.32/1.48  tff(c_38, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.48  tff(c_471, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_38])).
% 3.32/1.48  tff(c_40, plain, (r1_tarski('#skF_4', '#skF_3') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.48  tff(c_473, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_40])).
% 3.32/1.48  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.32/1.48  tff(c_480, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_42])).
% 3.32/1.48  tff(c_636, plain, (![A_122, B_123]: (k1_tops_1(A_122, B_123)=k1_xboole_0 | ~v2_tops_1(B_123, A_122) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.32/1.48  tff(c_646, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_636])).
% 3.32/1.48  tff(c_653, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_469, c_646])).
% 3.32/1.48  tff(c_861, plain, (![B_144, A_145, C_146]: (r1_tarski(B_144, k1_tops_1(A_145, C_146)) | ~r1_tarski(B_144, C_146) | ~v3_pre_topc(B_144, A_145) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.32/1.48  tff(c_868, plain, (![B_144]: (r1_tarski(B_144, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_144, '#skF_3') | ~v3_pre_topc(B_144, '#skF_2') | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_861])).
% 3.32/1.48  tff(c_927, plain, (![B_153]: (r1_tarski(B_153, k1_xboole_0) | ~r1_tarski(B_153, '#skF_3') | ~v3_pre_topc(B_153, '#skF_2') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_653, c_868])).
% 3.32/1.48  tff(c_934, plain, (r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_480, c_927])).
% 3.32/1.48  tff(c_941, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_471, c_473, c_934])).
% 3.32/1.48  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.32/1.48  tff(c_498, plain, (![B_102, A_103]: (B_102=A_103 | ~r1_tarski(B_102, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.32/1.48  tff(c_516, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_498])).
% 3.32/1.48  tff(c_952, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_941, c_516])).
% 3.32/1.48  tff(c_960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_468, c_952])).
% 3.32/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.48  
% 3.32/1.48  Inference rules
% 3.32/1.48  ----------------------
% 3.32/1.48  #Ref     : 0
% 3.32/1.48  #Sup     : 177
% 3.32/1.48  #Fact    : 0
% 3.32/1.48  #Define  : 0
% 3.32/1.48  #Split   : 13
% 3.32/1.48  #Chain   : 0
% 3.32/1.48  #Close   : 0
% 3.32/1.48  
% 3.32/1.48  Ordering : KBO
% 3.32/1.48  
% 3.32/1.48  Simplification rules
% 3.32/1.48  ----------------------
% 3.32/1.48  #Subsume      : 41
% 3.32/1.48  #Demod        : 103
% 3.32/1.48  #Tautology    : 45
% 3.32/1.48  #SimpNegUnit  : 9
% 3.32/1.48  #BackRed      : 3
% 3.32/1.48  
% 3.32/1.48  #Partial instantiations: 0
% 3.32/1.48  #Strategies tried      : 1
% 3.32/1.48  
% 3.32/1.48  Timing (in seconds)
% 3.32/1.48  ----------------------
% 3.32/1.49  Preprocessing        : 0.30
% 3.32/1.49  Parsing              : 0.16
% 3.32/1.49  CNF conversion       : 0.02
% 3.32/1.49  Main loop            : 0.39
% 3.32/1.49  Inferencing          : 0.14
% 3.32/1.49  Reduction            : 0.11
% 3.32/1.49  Demodulation         : 0.08
% 3.32/1.49  BG Simplification    : 0.02
% 3.32/1.49  Subsumption          : 0.09
% 3.32/1.49  Abstraction          : 0.02
% 3.32/1.49  MUC search           : 0.00
% 3.32/1.49  Cooper               : 0.00
% 3.32/1.49  Total                : 0.73
% 3.32/1.49  Index Insertion      : 0.00
% 3.32/1.49  Index Deletion       : 0.00
% 3.32/1.49  Index Matching       : 0.00
% 3.32/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
